%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 168 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  301 ( 665 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f69,f89,f97,f113,f115,f127,f130,f138])).

fof(f138,plain,
    ( spl6_1
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f136,f34])).

fof(f34,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v6_orders_2(sK5,sK4) )
    & r2_wellord1(u1_orders_2(sK4),sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X1,X0) )
            & r2_wellord1(u1_orders_2(X0),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
            | ~ v6_orders_2(X1,sK4) )
          & r2_wellord1(u1_orders_2(sK4),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          | ~ v6_orders_2(X1,sK4) )
        & r2_wellord1(u1_orders_2(sK4),X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ v6_orders_2(sK5,sK4) )
      & r2_wellord1(u1_orders_2(sK4),sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r2_wellord1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r2_wellord1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_wellord1(u1_orders_2(X0),X1)
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_wellord1(u1_orders_2(X0),X1)
           => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_orders_2)).

fof(f136,plain,
    ( ~ l1_orders_2(sK4)
    | spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f135,f61])).

fof(f61,plain,
    ( ~ v6_orders_2(sK5,sK4)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_1
  <=> v6_orders_2(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f135,plain,
    ( v6_orders_2(sK5,sK4)
    | ~ l1_orders_2(sK4)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f134,f126])).

fof(f126,plain,
    ( r7_relat_2(u1_orders_2(sK4),sK5)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_10
  <=> r7_relat_2(u1_orders_2(sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f134,plain,
    ( ~ r7_relat_2(u1_orders_2(sK4),sK5)
    | v6_orders_2(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(f130,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl6_9 ),
    inference(subsumption_resolution,[],[f128,f34])).

fof(f128,plain,
    ( ~ l1_orders_2(sK4)
    | spl6_9 ),
    inference(resolution,[],[f122,f93])).

fof(f93,plain,(
    ! [X0] :
      ( v1_relat_1(u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f92,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f92,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_relat_1(u1_orders_2(X0))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))) ) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f122,plain,
    ( ~ v1_relat_1(u1_orders_2(sK4))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_9
  <=> v1_relat_1(u1_orders_2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f127,plain,
    ( ~ spl6_9
    | spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f116,f110,f124,f120])).

fof(f110,plain,
    ( spl6_8
  <=> sP2(sK5,u1_orders_2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f116,plain,
    ( r7_relat_2(u1_orders_2(sK4),sK5)
    | ~ v1_relat_1(u1_orders_2(sK4))
    | ~ spl6_8 ),
    inference(resolution,[],[f112,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | r7_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f53,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f15,f20,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( r6_relat_2(X1,X0)
        & r1_relat_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ( r7_relat_2(X1,X0)
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | ~ sP2(X1,X0)
      | r7_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X0,X1)
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ~ r7_relat_2(X0,X1) ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | ~ r7_relat_2(X1,X0) ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f112,plain,
    ( sP2(sK5,u1_orders_2(sK4))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f115,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f108,f103])).

fof(f103,plain,
    ( r1_relat_2(u1_orders_2(sK4),sK5)
    | ~ spl6_6 ),
    inference(resolution,[],[f88,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r1_relat_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ r1_wellord1(X1,X0)
        | ~ r6_relat_2(X1,X0)
        | ~ r4_relat_2(X1,X0)
        | ~ r8_relat_2(X1,X0)
        | ~ r1_relat_2(X1,X0) )
      & ( ( r1_wellord1(X1,X0)
          & r6_relat_2(X1,X0)
          & r4_relat_2(X1,X0)
          & r8_relat_2(X1,X0)
          & r1_relat_2(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ~ r1_wellord1(X0,X1)
        | ~ r6_relat_2(X0,X1)
        | ~ r4_relat_2(X0,X1)
        | ~ r8_relat_2(X0,X1)
        | ~ r1_relat_2(X0,X1) )
      & ( ( r1_wellord1(X0,X1)
          & r6_relat_2(X0,X1)
          & r4_relat_2(X0,X1)
          & r8_relat_2(X0,X1)
          & r1_relat_2(X0,X1) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ~ r1_wellord1(X0,X1)
        | ~ r6_relat_2(X0,X1)
        | ~ r4_relat_2(X0,X1)
        | ~ r8_relat_2(X0,X1)
        | ~ r1_relat_2(X0,X1) )
      & ( ( r1_wellord1(X0,X1)
          & r6_relat_2(X0,X1)
          & r4_relat_2(X0,X1)
          & r8_relat_2(X0,X1)
          & r1_relat_2(X0,X1) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( r1_wellord1(X0,X1)
        & r6_relat_2(X0,X1)
        & r4_relat_2(X0,X1)
        & r8_relat_2(X0,X1)
        & r1_relat_2(X0,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f88,plain,
    ( sP0(sK5,u1_orders_2(sK4))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_6
  <=> sP0(sK5,u1_orders_2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f108,plain,
    ( ~ r1_relat_2(u1_orders_2(sK4),sK5)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_7
  <=> r1_relat_2(u1_orders_2(sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f113,plain,
    ( ~ spl6_7
    | spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f104,f86,f110,f106])).

fof(f104,plain,
    ( sP2(sK5,u1_orders_2(sK4))
    | ~ r1_relat_2(u1_orders_2(sK4),sK5)
    | ~ spl6_6 ),
    inference(resolution,[],[f100,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r6_relat_2(X1,X0)
      | sP2(X0,X1)
      | ~ r1_relat_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ r6_relat_2(X1,X0)
        | ~ r1_relat_2(X1,X0) )
      & ( ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ r6_relat_2(X1,X0)
        | ~ r1_relat_2(X1,X0) )
      & ( ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f100,plain,
    ( r6_relat_2(u1_orders_2(sK4),sK5)
    | ~ spl6_6 ),
    inference(resolution,[],[f88,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r6_relat_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f97,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl6_5 ),
    inference(subsumption_resolution,[],[f95,f34])).

fof(f95,plain,
    ( ~ l1_orders_2(sK4)
    | spl6_5 ),
    inference(resolution,[],[f94,f84])).

fof(f84,plain,
    ( ~ sP1(u1_orders_2(sK4))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_5
  <=> sP1(u1_orders_2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f94,plain,(
    ! [X0] :
      ( sP1(u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f93,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f14,f17,f16])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> sP0(X1,X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).

fof(f89,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f80,f86,f82])).

fof(f80,plain,
    ( sP0(sK5,u1_orders_2(sK4))
    | ~ sP1(u1_orders_2(sK4)) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    r2_wellord1(u1_orders_2(sK4),sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_wellord1(X0,X1)
      | sP0(X1,X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ sP0(X1,X0) )
          & ( sP0(X1,X0)
            | ~ r2_wellord1(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f69,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f65,f35])).

fof(f65,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_2
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f66,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f37,f63,f59])).

fof(f37,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v6_orders_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:31:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (25135)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.20/0.45  % (25126)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.46  % (25126)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f66,f69,f89,f97,f113,f115,f127,f130,f138])).
% 0.20/0.46  fof(f138,plain,(
% 0.20/0.46    spl6_1 | ~spl6_10),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f137])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    $false | (spl6_1 | ~spl6_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f136,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    l1_orders_2(sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ((~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~v6_orders_2(sK5,sK4)) & r2_wellord1(u1_orders_2(sK4),sK5) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_orders_2(sK4)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f23,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X1,X0)) & r2_wellord1(u1_orders_2(X0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) | ~v6_orders_2(X1,sK4)) & r2_wellord1(u1_orders_2(sK4),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_orders_2(sK4))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) | ~v6_orders_2(X1,sK4)) & r2_wellord1(u1_orders_2(sK4),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) => ((~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~v6_orders_2(sK5,sK4)) & r2_wellord1(u1_orders_2(sK4),sK5) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X1,X0)) & r2_wellord1(u1_orders_2(X0),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0))),
% 0.20/0.46    inference(flattening,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X1,X0)) & r2_wellord1(u1_orders_2(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_wellord1(u1_orders_2(X0),X1) => (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f7])).
% 0.20/0.46  fof(f7,conjecture,(
% 0.20/0.46    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_wellord1(u1_orders_2(X0),X1) => (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X1,X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_orders_2)).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    ~l1_orders_2(sK4) | (spl6_1 | ~spl6_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f135,f61])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ~v6_orders_2(sK5,sK4) | spl6_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    spl6_1 <=> v6_orders_2(sK5,sK4)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.46  fof(f135,plain,(
% 0.20/0.46    v6_orders_2(sK5,sK4) | ~l1_orders_2(sK4) | ~spl6_10),
% 0.20/0.46    inference(subsumption_resolution,[],[f134,f126])).
% 0.20/0.46  fof(f126,plain,(
% 0.20/0.46    r7_relat_2(u1_orders_2(sK4),sK5) | ~spl6_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f124])).
% 0.20/0.46  fof(f124,plain,(
% 0.20/0.46    spl6_10 <=> r7_relat_2(u1_orders_2(sK4),sK5)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.46  fof(f134,plain,(
% 0.20/0.46    ~r7_relat_2(u1_orders_2(sK4),sK5) | v6_orders_2(sK5,sK4) | ~l1_orders_2(sK4)),
% 0.20/0.46    inference(resolution,[],[f40,f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r7_relat_2(u1_orders_2(X0),X1) | v6_orders_2(X1,X0) | ~l1_orders_2(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (((v6_orders_2(X1,X0) | ~r7_relat_2(u1_orders_2(X0),X1)) & (r7_relat_2(u1_orders_2(X0),X1) | ~v6_orders_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_orders_2(X1,X0) <=> r7_relat_2(u1_orders_2(X0),X1))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).
% 0.20/0.46  fof(f130,plain,(
% 0.20/0.46    spl6_9),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f129])).
% 0.20/0.46  fof(f129,plain,(
% 0.20/0.46    $false | spl6_9),
% 0.20/0.46    inference(subsumption_resolution,[],[f128,f34])).
% 0.20/0.46  fof(f128,plain,(
% 0.20/0.46    ~l1_orders_2(sK4) | spl6_9),
% 0.20/0.46    inference(resolution,[],[f122,f93])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f92,f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_orders_2(X0) | v1_relat_1(u1_orders_2(X0)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )),
% 0.20/0.46    inference(resolution,[],[f38,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    ~v1_relat_1(u1_orders_2(sK4)) | spl6_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f120])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    spl6_9 <=> v1_relat_1(u1_orders_2(sK4))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.46  fof(f127,plain,(
% 0.20/0.46    ~spl6_9 | spl6_10 | ~spl6_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f116,f110,f124,f120])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    spl6_8 <=> sP2(sK5,u1_orders_2(sK4))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    r7_relat_2(u1_orders_2(sK4),sK5) | ~v1_relat_1(u1_orders_2(sK4)) | ~spl6_8),
% 0.20/0.46    inference(resolution,[],[f112,f91])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~sP2(X0,X1) | r7_relat_2(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(resolution,[],[f53,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(definition_folding,[],[f15,f20,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1] : (sP2(X0,X1) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0)))),
% 0.20/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X1,X0] : ((r7_relat_2(X1,X0) <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 0.20/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : ((r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r7_relat_2(X1,X0) <=> (r6_relat_2(X1,X0) & r1_relat_2(X1,X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~sP3(X0,X1) | ~sP2(X1,X0) | r7_relat_2(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ! [X0,X1] : (((r7_relat_2(X0,X1) | ~sP2(X1,X0)) & (sP2(X1,X0) | ~r7_relat_2(X0,X1))) | ~sP3(X0,X1))),
% 0.20/0.46    inference(rectify,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ! [X1,X0] : (((r7_relat_2(X1,X0) | ~sP2(X0,X1)) & (sP2(X0,X1) | ~r7_relat_2(X1,X0))) | ~sP3(X1,X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f20])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    sP2(sK5,u1_orders_2(sK4)) | ~spl6_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f110])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    ~spl6_6 | spl6_7),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f114])).
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    $false | (~spl6_6 | spl6_7)),
% 0.20/0.46    inference(subsumption_resolution,[],[f108,f103])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    r1_relat_2(u1_orders_2(sK4),sK5) | ~spl6_6),
% 0.20/0.46    inference(resolution,[],[f88,f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~sP0(X0,X1) | r1_relat_2(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0,X1] : ((sP0(X0,X1) | ~r1_wellord1(X1,X0) | ~r6_relat_2(X1,X0) | ~r4_relat_2(X1,X0) | ~r8_relat_2(X1,X0) | ~r1_relat_2(X1,X0)) & ((r1_wellord1(X1,X0) & r6_relat_2(X1,X0) & r4_relat_2(X1,X0) & r8_relat_2(X1,X0) & r1_relat_2(X1,X0)) | ~sP0(X0,X1)))),
% 0.20/0.46    inference(rectify,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X1,X0] : ((sP0(X1,X0) | ~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1)) & ((r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~sP0(X1,X0)))),
% 0.20/0.46    inference(flattening,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X1,X0] : ((sP0(X1,X0) | (~r1_wellord1(X0,X1) | ~r6_relat_2(X0,X1) | ~r4_relat_2(X0,X1) | ~r8_relat_2(X0,X1) | ~r1_relat_2(X0,X1))) & ((r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)) | ~sP0(X1,X0)))),
% 0.20/0.46    inference(nnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X1,X0] : (sP0(X1,X0) <=> (r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1)))),
% 0.20/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    sP0(sK5,u1_orders_2(sK4)) | ~spl6_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f86])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    spl6_6 <=> sP0(sK5,u1_orders_2(sK4))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    ~r1_relat_2(u1_orders_2(sK4),sK5) | spl6_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f106])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    spl6_7 <=> r1_relat_2(u1_orders_2(sK4),sK5)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    ~spl6_7 | spl6_8 | ~spl6_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f104,f86,f110,f106])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    sP2(sK5,u1_orders_2(sK4)) | ~r1_relat_2(u1_orders_2(sK4),sK5) | ~spl6_6),
% 0.20/0.46    inference(resolution,[],[f100,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r6_relat_2(X1,X0) | sP2(X0,X1) | ~r1_relat_2(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ! [X0,X1] : ((sP2(X0,X1) | ~r6_relat_2(X1,X0) | ~r1_relat_2(X1,X0)) & ((r6_relat_2(X1,X0) & r1_relat_2(X1,X0)) | ~sP2(X0,X1)))),
% 0.20/0.46    inference(flattening,[],[f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ! [X0,X1] : ((sP2(X0,X1) | (~r6_relat_2(X1,X0) | ~r1_relat_2(X1,X0))) & ((r6_relat_2(X1,X0) & r1_relat_2(X1,X0)) | ~sP2(X0,X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f19])).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    r6_relat_2(u1_orders_2(sK4),sK5) | ~spl6_6),
% 0.20/0.46    inference(resolution,[],[f88,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~sP0(X0,X1) | r6_relat_2(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f29])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    spl6_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f96])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    $false | spl6_5),
% 0.20/0.46    inference(subsumption_resolution,[],[f95,f34])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    ~l1_orders_2(sK4) | spl6_5),
% 0.20/0.46    inference(resolution,[],[f94,f84])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    ~sP1(u1_orders_2(sK4)) | spl6_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f82])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    spl6_5 <=> sP1(u1_orders_2(sK4))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    ( ! [X0] : (sP1(u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.46    inference(resolution,[],[f93,f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_relat_1(X0) | sP1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(definition_folding,[],[f14,f17,f16])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (r2_wellord1(X0,X1) <=> sP0(X1,X0)) | ~sP1(X0))),
% 0.20/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (r2_wellord1(X0,X1) <=> (r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_wellord1(X0,X1) <=> (r1_wellord1(X0,X1) & r6_relat_2(X0,X1) & r4_relat_2(X0,X1) & r8_relat_2(X0,X1) & r1_relat_2(X0,X1))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    ~spl6_5 | spl6_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f80,f86,f82])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    sP0(sK5,u1_orders_2(sK4)) | ~sP1(u1_orders_2(sK4))),
% 0.20/0.46    inference(resolution,[],[f42,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    r2_wellord1(u1_orders_2(sK4),sK5)),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_wellord1(X0,X1) | sP0(X1,X0) | ~sP1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((r2_wellord1(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~r2_wellord1(X0,X1))) | ~sP1(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f17])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    spl6_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    $false | spl6_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f65,f35])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | spl6_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    spl6_2 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ~spl6_1 | ~spl6_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f37,f63,f59])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | ~v6_orders_2(sK5,sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (25126)------------------------------
% 0.20/0.46  % (25126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (25126)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (25126)Memory used [KB]: 5373
% 0.20/0.46  % (25126)Time elapsed: 0.059 s
% 0.20/0.46  % (25126)------------------------------
% 0.20/0.46  % (25126)------------------------------
% 0.20/0.46  % (25118)Success in time 0.109 s
%------------------------------------------------------------------------------
