%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1185+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 274 expanded)
%              Number of leaves         :   19 (  75 expanded)
%              Depth                    :   22
%              Number of atoms          :  380 (1354 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f107,f136])).

fof(f136,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f134,f108])).

fof(f108,plain,
    ( sP1(u1_orders_2(sK4))
    | ~ spl6_1 ),
    inference(resolution,[],[f98,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f22,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( r6_relat_2(X0,X1)
        & r4_relat_2(X0,X1)
        & r8_relat_2(X0,X1)
        & r1_relat_2(X0,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> sP0(X1,X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_orders_1)).

fof(f98,plain,
    ( v1_relat_1(u1_orders_2(sK4))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_1
  <=> v1_relat_1(u1_orders_2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f134,plain,
    ( ~ sP1(u1_orders_2(sK4))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f129,f55])).

fof(f55,plain,(
    ~ r3_orders_1(u1_orders_2(sK4),sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r3_orders_1(u1_orders_2(sK4),sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v6_orders_2(sK5,sK4)
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f17,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_orders_1(u1_orders_2(X0),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(sK4),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & v6_orders_2(X1,sK4) )
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ~ r3_orders_1(u1_orders_2(sK4),X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
        & v6_orders_2(X1,sK4) )
   => ( ~ r3_orders_1(u1_orders_2(sK4),sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
      & v6_orders_2(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
         => r3_orders_1(u1_orders_2(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_orders_2)).

fof(f129,plain,
    ( r3_orders_1(u1_orders_2(sK4),sK5)
    | ~ sP1(u1_orders_2(sK4))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f128,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,X0)
      | r3_orders_1(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_orders_1(X0,X1)
            | ~ sP0(X1,X0) )
          & ( sP0(X1,X0)
            | ~ r3_orders_1(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f128,plain,
    ( sP0(sK5,u1_orders_2(sK4))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f127,f122])).

fof(f122,plain,
    ( r1_relat_2(u1_orders_2(sK4),sK5)
    | ~ spl6_1 ),
    inference(resolution,[],[f119,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | r1_relat_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ r6_relat_2(X1,X0)
        | ~ r1_relat_2(X1,X0) )
      & ( ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ r6_relat_2(X1,X0)
        | ~ r1_relat_2(X1,X0) )
      & ( ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( r6_relat_2(X1,X0)
        & r1_relat_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f119,plain,
    ( sP2(sK5,u1_orders_2(sK4))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f118,f98])).

fof(f118,plain,
    ( sP2(sK5,u1_orders_2(sK4))
    | ~ v1_relat_1(u1_orders_2(sK4)) ),
    inference(resolution,[],[f117,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(X0,X1)
      | sP2(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f71,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f23,f34,f33])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( r7_relat_2(X1,X0)
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | ~ r7_relat_2(X0,X1)
      | sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X0,X1)
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ~ r7_relat_2(X0,X1) ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | ~ r7_relat_2(X1,X0) ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f117,plain,(
    r7_relat_2(u1_orders_2(sK4),sK5) ),
    inference(subsumption_resolution,[],[f116,f52])).

fof(f52,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f116,plain,
    ( r7_relat_2(u1_orders_2(sK4),sK5)
    | ~ l1_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f115,f53])).

fof(f53,plain,(
    v6_orders_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,
    ( ~ v6_orders_2(sK5,sK4)
    | r7_relat_2(u1_orders_2(sK4),sK5)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f61,f54])).

fof(f54,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X1,X0)
      | r7_relat_2(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(f127,plain,
    ( sP0(sK5,u1_orders_2(sK4))
    | ~ r1_relat_2(u1_orders_2(sK4),sK5)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f126,f114])).

fof(f114,plain,
    ( r8_relat_2(u1_orders_2(sK4),sK5)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f113,f52])).

fof(f113,plain,
    ( r8_relat_2(u1_orders_2(sK4),sK5)
    | ~ l1_orders_2(sK4)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f112,f50])).

fof(f50,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f112,plain,
    ( r8_relat_2(u1_orders_2(sK4),sK5)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f111,f98])).

fof(f111,plain,
    ( r8_relat_2(u1_orders_2(sK4),sK5)
    | ~ v1_relat_1(u1_orders_2(sK4))
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f109,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).

fof(f109,plain,(
    ! [X0] :
      ( ~ r8_relat_2(X0,u1_struct_0(sK4))
      | r8_relat_2(X0,sK5)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f79,f81])).

fof(f81,plain,(
    r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f77,f54])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r8_relat_2(X2,X1)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r8_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r8_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r8_relat_2(X2,X0) )
       => r8_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_orders_1)).

fof(f126,plain,
    ( sP0(sK5,u1_orders_2(sK4))
    | ~ r8_relat_2(u1_orders_2(sK4),sK5)
    | ~ r1_relat_2(u1_orders_2(sK4),sK5)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f125,f103])).

fof(f103,plain,
    ( r4_relat_2(u1_orders_2(sK4),sK5)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_2
  <=> r4_relat_2(u1_orders_2(sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f125,plain,
    ( sP0(sK5,u1_orders_2(sK4))
    | ~ r4_relat_2(u1_orders_2(sK4),sK5)
    | ~ r8_relat_2(u1_orders_2(sK4),sK5)
    | ~ r1_relat_2(u1_orders_2(sK4),sK5)
    | ~ spl6_1 ),
    inference(resolution,[],[f69,f121])).

fof(f121,plain,
    ( r6_relat_2(u1_orders_2(sK4),sK5)
    | ~ spl6_1 ),
    inference(resolution,[],[f119,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | r6_relat_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r6_relat_2(X1,X0)
      | sP0(X0,X1)
      | ~ r4_relat_2(X1,X0)
      | ~ r8_relat_2(X1,X0)
      | ~ r1_relat_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ r6_relat_2(X1,X0)
        | ~ r4_relat_2(X1,X0)
        | ~ r8_relat_2(X1,X0)
        | ~ r1_relat_2(X1,X0) )
      & ( ( r6_relat_2(X1,X0)
          & r4_relat_2(X1,X0)
          & r8_relat_2(X1,X0)
          & r1_relat_2(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ~ r6_relat_2(X0,X1)
        | ~ r4_relat_2(X0,X1)
        | ~ r8_relat_2(X0,X1)
        | ~ r1_relat_2(X0,X1) )
      & ( ( r6_relat_2(X0,X1)
          & r4_relat_2(X0,X1)
          & r8_relat_2(X0,X1)
          & r1_relat_2(X0,X1) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ~ r6_relat_2(X0,X1)
        | ~ r4_relat_2(X0,X1)
        | ~ r8_relat_2(X0,X1)
        | ~ r1_relat_2(X0,X1) )
      & ( ( r6_relat_2(X0,X1)
          & r4_relat_2(X0,X1)
          & r8_relat_2(X0,X1)
          & r1_relat_2(X0,X1) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f107,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f105,f52])).

fof(f105,plain,
    ( ~ l1_orders_2(sK4)
    | spl6_1 ),
    inference(resolution,[],[f99,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v1_relat_1(u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f56,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f99,plain,
    ( ~ v1_relat_1(u1_orders_2(sK4))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f104,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f95,f101,f97])).

fof(f95,plain,
    ( r4_relat_2(u1_orders_2(sK4),sK5)
    | ~ v1_relat_1(u1_orders_2(sK4)) ),
    inference(subsumption_resolution,[],[f94,f52])).

fof(f94,plain,
    ( r4_relat_2(u1_orders_2(sK4),sK5)
    | ~ v1_relat_1(u1_orders_2(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f93,f51])).

fof(f51,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,
    ( r4_relat_2(u1_orders_2(sK4),sK5)
    | ~ v1_relat_1(u1_orders_2(sK4))
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f91,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v5_orders_2(X0)
          | ~ r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v5_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

fof(f91,plain,(
    ! [X0] :
      ( ~ r4_relat_2(X0,u1_struct_0(sK4))
      | r4_relat_2(X0,sK5)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f78,f81])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r4_relat_2(X2,X1)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r4_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r4_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r4_relat_2(X2,X0) )
       => r4_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_orders_1)).

%------------------------------------------------------------------------------
