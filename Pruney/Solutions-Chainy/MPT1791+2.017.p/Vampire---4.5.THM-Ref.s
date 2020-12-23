%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 524 expanded)
%              Number of leaves         :   17 ( 156 expanded)
%              Depth                    :   18
%              Number of atoms          :  416 (3565 expanded)
%              Number of equality atoms :   55 ( 759 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f733,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f92,f650,f731])).

fof(f731,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f729])).

fof(f729,plain,
    ( $false
    | spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f684,f48,f675,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f675,plain,
    ( u1_pre_topc(sK2) = k5_tmap_1(sK2,sK3)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f213,f657])).

fof(f657,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(k6_tmap_1(sK2,sK3))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f335,f651])).

fof(f651,plain,
    ( k6_tmap_1(sK2,sK3) = k6_tmap_1(sK2,u1_struct_0(sK2))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f330,f89])).

fof(f89,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_2
  <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f330,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f318,f328])).

fof(f328,plain,(
    u1_pre_topc(sK2) = k5_tmap_1(sK2,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f99,f93,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f52,f51])).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f99,plain,(
    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(unit_resulting_resolution,[],[f95,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),sK5(X0)),u1_pre_topc(X0))
          & r2_hidden(sK5(X0),u1_pre_topc(X0))
          & r2_hidden(sK4(X0),u1_pre_topc(X0))
          & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) )
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0))
          & r1_tarski(sK6(X0),u1_pre_topc(X0))
          & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f38,f41,f40,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK4(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK4(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),sK5(X0)),u1_pre_topc(X0))
        & r2_hidden(sK5(X0),u1_pre_topc(X0))
        & r2_hidden(sK4(X0),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0))
        & r1_tarski(sK6(X0),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
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
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
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
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP0(X0)
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
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f95,plain,(
    sP0(sK2) ),
    inference(unit_resulting_resolution,[],[f94,f46,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f94,plain,(
    sP1(sK2) ),
    inference(unit_resulting_resolution,[],[f47,f74])).

fof(f74,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f17,f28,f27])).

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
    inference(flattening,[],[f16])).

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
    inference(ennf_transformation,[],[f12])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f318,plain,(
    k6_tmap_1(sK2,u1_struct_0(sK2)) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK2))) ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f93,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f335,plain,(
    u1_pre_topc(sK2) = u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f212,f328])).

fof(f212,plain,(
    u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK2))) = k5_tmap_1(sK2,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f93,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f213,plain,(
    u1_pre_topc(k6_tmap_1(sK2,sK3)) = k5_tmap_1(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f79])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3)
      | ~ v3_pre_topc(sK3,sK2) )
    & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)
      | v3_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f33,f32])).

fof(f32,plain,
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
          ( ( k6_tmap_1(sK2,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
            | ~ v3_pre_topc(X1,sK2) )
          & ( k6_tmap_1(sK2,X1) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
            | v3_pre_topc(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( k6_tmap_1(sK2,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
          | ~ v3_pre_topc(X1,sK2) )
        & ( k6_tmap_1(sK2,X1) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
          | v3_pre_topc(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3)
        | ~ v3_pre_topc(sK3,sK2) )
      & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)
        | v3_pre_topc(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

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

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f684,plain,
    ( ~ r2_hidden(sK3,u1_pre_topc(sK2))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f47,f48,f86,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f86,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_1
  <=> v3_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f650,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f90,f641])).

fof(f641,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f319,f635])).

fof(f635,plain,
    ( u1_pre_topc(sK2) = k5_tmap_1(sK2,sK3)
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f632,f80])).

fof(f632,plain,
    ( r2_hidden(sK3,u1_pre_topc(sK2))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f47,f48,f85,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f319,plain,(
    k6_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f77])).

fof(f90,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f92,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f49,f88,f84])).

fof(f49,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)
    | v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f50,f88,f84])).

fof(f50,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3)
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (11381)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.46  % (11388)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.48  % (11388)Refutation not found, incomplete strategy% (11388)------------------------------
% 0.20/0.48  % (11388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (11388)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (11388)Memory used [KB]: 10618
% 0.20/0.48  % (11388)Time elapsed: 0.064 s
% 0.20/0.48  % (11388)------------------------------
% 0.20/0.48  % (11388)------------------------------
% 0.20/0.49  % (11403)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.49  % (11385)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (11394)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (11400)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.50  % (11397)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (11398)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  % (11382)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (11380)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (11384)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.51  % (11403)Refutation not found, incomplete strategy% (11403)------------------------------
% 0.20/0.51  % (11403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11403)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11403)Memory used [KB]: 10618
% 0.20/0.51  % (11403)Time elapsed: 0.062 s
% 0.20/0.51  % (11403)------------------------------
% 0.20/0.51  % (11403)------------------------------
% 0.20/0.51  % (11383)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (11401)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.51  % (11383)Refutation not found, incomplete strategy% (11383)------------------------------
% 0.20/0.51  % (11383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11383)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11383)Memory used [KB]: 10618
% 0.20/0.51  % (11383)Time elapsed: 0.103 s
% 0.20/0.51  % (11383)------------------------------
% 0.20/0.51  % (11383)------------------------------
% 0.20/0.51  % (11387)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (11387)Refutation not found, incomplete strategy% (11387)------------------------------
% 0.20/0.51  % (11387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11387)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11387)Memory used [KB]: 6140
% 0.20/0.51  % (11387)Time elapsed: 0.106 s
% 0.20/0.51  % (11387)------------------------------
% 0.20/0.51  % (11387)------------------------------
% 0.20/0.51  % (11396)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (11401)Refutation not found, incomplete strategy% (11401)------------------------------
% 0.20/0.51  % (11401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11401)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11401)Memory used [KB]: 1663
% 0.20/0.51  % (11401)Time elapsed: 0.111 s
% 0.20/0.51  % (11401)------------------------------
% 0.20/0.51  % (11401)------------------------------
% 0.20/0.51  % (11392)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % (11389)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (11402)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (11396)Refutation not found, incomplete strategy% (11396)------------------------------
% 0.20/0.51  % (11396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11396)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11396)Memory used [KB]: 1663
% 0.20/0.51  % (11396)Time elapsed: 0.107 s
% 0.20/0.51  % (11396)------------------------------
% 0.20/0.51  % (11396)------------------------------
% 0.20/0.52  % (11394)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f733,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f91,f92,f650,f731])).
% 0.20/0.52  fof(f731,plain,(
% 0.20/0.52    spl7_1 | ~spl7_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f729])).
% 0.20/0.52  fof(f729,plain,(
% 0.20/0.52    $false | (spl7_1 | ~spl7_2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f45,f46,f47,f684,f48,f675,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r2_hidden(X1,u1_pre_topc(X0)) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.20/0.52  fof(f675,plain,(
% 0.20/0.52    u1_pre_topc(sK2) = k5_tmap_1(sK2,sK3) | ~spl7_2),
% 0.20/0.52    inference(backward_demodulation,[],[f213,f657])).
% 0.20/0.52  fof(f657,plain,(
% 0.20/0.52    u1_pre_topc(sK2) = u1_pre_topc(k6_tmap_1(sK2,sK3)) | ~spl7_2),
% 0.20/0.52    inference(backward_demodulation,[],[f335,f651])).
% 0.20/0.52  fof(f651,plain,(
% 0.20/0.52    k6_tmap_1(sK2,sK3) = k6_tmap_1(sK2,u1_struct_0(sK2)) | ~spl7_2),
% 0.20/0.52    inference(backward_demodulation,[],[f330,f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) | ~spl7_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl7_2 <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.52  fof(f330,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(sK2))),
% 0.20/0.52    inference(backward_demodulation,[],[f318,f328])).
% 0.20/0.52  fof(f328,plain,(
% 0.20/0.52    u1_pre_topc(sK2) = k5_tmap_1(sK2,u1_struct_0(sK2))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f45,f46,f47,f99,f93,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f52,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    r2_hidden(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f95,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0] : ((sP0(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),sK5(X0)),u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0)) & r1_tarski(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f38,f41,f40,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),sK5(X0)),u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & r2_hidden(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0] : (? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0)) & r1_tarski(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.20/0.52    inference(rectify,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.20/0.52    inference(flattening,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0] : ((sP0(X0) | (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (sP0(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    sP0(sK2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f94,f46,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0] : (~v2_pre_topc(X0) | sP0(X0) | ~sP1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_pre_topc(X0))) | ~sP1(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : ((v2_pre_topc(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    sP1(sK2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f47,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X0] : (sP1(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (sP1(X0) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(definition_folding,[],[f17,f28,f27])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.52    inference(rectify,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.20/0.52  fof(f318,plain,(
% 0.20/0.52    k6_tmap_1(sK2,u1_struct_0(sK2)) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK2)))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f45,f46,f47,f93,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).
% 0.20/0.52  fof(f335,plain,(
% 0.20/0.52    u1_pre_topc(sK2) = u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK2)))),
% 0.20/0.52    inference(backward_demodulation,[],[f212,f328])).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK2))) = k5_tmap_1(sK2,u1_struct_0(sK2))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f45,f46,f47,f93,f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.20/0.52  fof(f213,plain,(
% 0.20/0.52    u1_pre_topc(k6_tmap_1(sK2,sK3)) = k5_tmap_1(sK2,sK3)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f79])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3) | ~v3_pre_topc(sK3,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f33,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k6_tmap_1(sK2,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~v3_pre_topc(X1,sK2)) & (k6_tmap_1(sK2,X1) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ? [X1] : ((k6_tmap_1(sK2,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | ~v3_pre_topc(X1,sK2)) & (k6_tmap_1(sK2,X1) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3) | ~v3_pre_topc(sK3,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.20/0.52  fof(f684,plain,(
% 0.20/0.52    ~r2_hidden(sK3,u1_pre_topc(sK2)) | spl7_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f47,f48,f86,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ~v3_pre_topc(sK3,sK2) | spl7_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    spl7_1 <=> v3_pre_topc(sK3,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    l1_pre_topc(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    v2_pre_topc(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ~v2_struct_0(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f650,plain,(
% 0.20/0.52    ~spl7_1 | spl7_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f648])).
% 0.20/0.52  fof(f648,plain,(
% 0.20/0.52    $false | (~spl7_1 | spl7_2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f90,f641])).
% 0.20/0.52  fof(f641,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) | ~spl7_1),
% 0.20/0.52    inference(backward_demodulation,[],[f319,f635])).
% 0.20/0.52  fof(f635,plain,(
% 0.20/0.52    u1_pre_topc(sK2) = k5_tmap_1(sK2,sK3) | ~spl7_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f632,f80])).
% 0.20/0.52  fof(f632,plain,(
% 0.20/0.52    r2_hidden(sK3,u1_pre_topc(sK2)) | ~spl7_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f47,f48,f85,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    v3_pre_topc(sK3,sK2) | ~spl7_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f84])).
% 0.20/0.52  fof(f319,plain,(
% 0.20/0.52    k6_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,sK3))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f45,f46,f47,f48,f77])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3) | spl7_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f88])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    spl7_1 | spl7_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f49,f88,f84])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) | v3_pre_topc(sK3,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ~spl7_1 | ~spl7_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f50,f88,f84])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3) | ~v3_pre_topc(sK3,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (11394)------------------------------
% 0.20/0.52  % (11394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11394)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (11394)Memory used [KB]: 11001
% 0.20/0.52  % (11394)Time elapsed: 0.081 s
% 0.20/0.52  % (11394)------------------------------
% 0.20/0.52  % (11394)------------------------------
% 0.20/0.52  % (11379)Success in time 0.159 s
%------------------------------------------------------------------------------
