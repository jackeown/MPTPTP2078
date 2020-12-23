%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 190 expanded)
%              Number of leaves         :   29 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  347 ( 544 expanded)
%              Number of equality atoms :   51 (  98 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f55,f59,f64,f68,f72,f76,f84,f97,f101,f123,f128,f160,f167,f174,f200,f244,f259])).

fof(f259,plain,
    ( ~ spl1_1
    | spl1_2
    | ~ spl1_30 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl1_1
    | spl1_2
    | ~ spl1_30 ),
    inference(subsumption_resolution,[],[f50,f245])).

fof(f245,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))
    | ~ spl1_1
    | ~ spl1_30 ),
    inference(unit_resulting_resolution,[],[f45,f243])).

fof(f243,plain,
    ( ! [X1] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ l1_orders_2(X1) )
    | ~ spl1_30 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl1_30
  <=> ! [X1] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).

fof(f45,plain,
    ( l1_orders_2(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl1_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f50,plain,
    ( k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_2
  <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f244,plain,
    ( spl1_30
    | ~ spl1_12
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_13
    | ~ spl1_17
    | ~ spl1_18
    | ~ spl1_21
    | ~ spl1_22
    | ~ spl1_23
    | ~ spl1_25 ),
    inference(avatar_split_clause,[],[f208,f198,f171,f164,f157,f126,f121,f99,f82,f74,f94,f242])).

fof(f94,plain,
    ( spl1_12
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f74,plain,
    ( spl1_8
  <=> ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f82,plain,
    ( spl1_10
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f99,plain,
    ( spl1_13
  <=> ! [X1,X0] :
        ( v1_yellow_1(k7_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f121,plain,
    ( spl1_17
  <=> ! [X1,X0] :
        ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f126,plain,
    ( spl1_18
  <=> ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f157,plain,
    ( spl1_21
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f164,plain,
    ( spl1_22
  <=> v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f171,plain,
    ( spl1_23
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f198,plain,
    ( spl1_25
  <=> ! [X0] : k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).

fof(f208,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k1_xboole_0)
        | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ l1_orders_2(X1) )
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_13
    | ~ spl1_17
    | ~ spl1_18
    | ~ spl1_21
    | ~ spl1_22
    | ~ spl1_23
    | ~ spl1_25 ),
    inference(subsumption_resolution,[],[f175,f204])).

fof(f204,plain,
    ( ! [X2] :
        ( v1_yellow_1(k1_xboole_0)
        | ~ l1_orders_2(X2) )
    | ~ spl1_13
    | ~ spl1_25 ),
    inference(superposition,[],[f100,f199])).

fof(f199,plain,
    ( ! [X0] : k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)
    | ~ spl1_25 ),
    inference(avatar_component_clause,[],[f198])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( v1_yellow_1(k7_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f175,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k1_xboole_0)
        | ~ v1_yellow_1(k1_xboole_0)
        | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ l1_orders_2(X1) )
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_17
    | ~ spl1_18
    | ~ spl1_21
    | ~ spl1_22
    | ~ spl1_23 ),
    inference(subsumption_resolution,[],[f168,f173])).

fof(f173,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f171])).

fof(f168,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k1_xboole_0)
        | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k1_xboole_0)
        | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ l1_orders_2(X1) )
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_17
    | ~ spl1_18
    | ~ spl1_21
    | ~ spl1_22 ),
    inference(subsumption_resolution,[],[f161,f166])).

fof(f166,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f164])).

fof(f161,plain,
    ( ! [X1] :
        ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k1_xboole_0)
        | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ l1_orders_2(X1) )
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_17
    | ~ spl1_18
    | ~ spl1_21 ),
    inference(subsumption_resolution,[],[f138,f159])).

fof(f159,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_21 ),
    inference(avatar_component_clause,[],[f157])).

fof(f138,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k1_xboole_0)
        | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k1_xboole_0)
        | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ l1_orders_2(X1) )
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_17
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f137,f102])).

fof(f102,plain,
    ( ! [X0] : k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(unit_resulting_resolution,[],[f75,f83])).

fof(f83,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f75,plain,
    ( ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f137,plain,
    ( ! [X1] :
        ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k1_xboole_0)
        | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_17
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f136,f102])).

fof(f136,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k1_xboole_0)
        | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k1_xboole_0)
        | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_17
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f135,f102])).

fof(f135,plain,
    ( ! [X1] :
        ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_yellow_1(k1_xboole_0)
        | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_17
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f134,f102])).

fof(f134,plain,
    ( ! [X1] :
        ( ~ v1_yellow_1(k1_xboole_0)
        | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_17
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f129,f102])).

fof(f129,plain,
    ( ! [X1] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1)
        | ~ v1_yellow_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_funct_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0)
        | ~ v1_relat_1(k7_funcop_1(k1_xboole_0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl1_17
    | ~ spl1_18 ),
    inference(superposition,[],[f127,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
        | ~ l1_orders_2(X1) )
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f121])).

fof(f127,plain,
    ( ! [X0] :
        ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))
        | ~ v1_yellow_1(X0)
        | ~ v1_partfun1(X0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v4_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f126])).

fof(f200,plain,
    ( spl1_25
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f102,f82,f74,f198])).

fof(f174,plain,
    ( spl1_23
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f88,f70,f61,f171])).

fof(f61,plain,
    ( spl1_5
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f70,plain,
    ( spl1_7
  <=> ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f88,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(superposition,[],[f71,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f71,plain,
    ( ! [X0] : v1_partfun1(k6_relat_1(X0),X0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f167,plain,
    ( spl1_22
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f87,f66,f61,f164])).

fof(f66,plain,
    ( spl1_6
  <=> ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f87,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(superposition,[],[f67,f63])).

fof(f67,plain,
    ( ! [X0] : v4_relat_1(k6_relat_1(X0),X0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f160,plain,
    ( spl1_21
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f86,f61,f53,f157])).

fof(f53,plain,
    ( spl1_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f86,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(superposition,[],[f54,f63])).

fof(f54,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f128,plain,(
    spl1_18 ),
    inference(avatar_split_clause,[],[f40,f126])).

fof(f40,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f33,f26])).

fof(f26,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f33,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(X0)
      | ~ v1_partfun1(X0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_yellow_1(X0)
        & v1_partfun1(X0,k1_xboole_0)
        & v1_funct_1(X0)
        & v4_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
     => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).

fof(f123,plain,(
    spl1_17 ),
    inference(avatar_split_clause,[],[f37,f121])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).

fof(f101,plain,(
    spl1_13 ),
    inference(avatar_split_clause,[],[f41,f99])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k7_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(forward_demodulation,[],[f36,f34])).

fof(f34,plain,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_yellow_1(k2_funcop_1(X0,X1))
      | ~ l1_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
     => v1_yellow_1(k2_funcop_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).

fof(f97,plain,
    ( spl1_12
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f85,f61,f57,f94])).

fof(f57,plain,
    ( spl1_4
  <=> ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f85,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(superposition,[],[f58,f63])).

fof(f58,plain,
    ( ! [X0] : v1_funct_1(k6_relat_1(X0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f84,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f76,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f25,f34])).

fof(f25,plain,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).

fof(f72,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_partfun1(k6_relat_1(X0),X0)
      & v1_funct_1(k6_relat_1(X0))
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_funct_2)).

fof(f68,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f24,f61])).

fof(f24,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f59,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ~ spl1_2 ),
    inference(avatar_split_clause,[],[f38,f48])).

fof(f38,plain,(
    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f23,f26])).

fof(f23,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
        & l1_orders_2(X0) )
   => ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0)
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).

fof(f46,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.41  % (30242)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.43  % (30237)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.44  % (30237)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f260,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f46,f51,f55,f59,f64,f68,f72,f76,f84,f97,f101,f123,f128,f160,f167,f174,f200,f244,f259])).
% 0.22/0.44  fof(f259,plain,(
% 0.22/0.44    ~spl1_1 | spl1_2 | ~spl1_30),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f258])).
% 0.22/0.44  fof(f258,plain,(
% 0.22/0.44    $false | (~spl1_1 | spl1_2 | ~spl1_30)),
% 0.22/0.44    inference(subsumption_resolution,[],[f50,f245])).
% 0.22/0.44  fof(f245,plain,(
% 0.22/0.44    k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) | (~spl1_1 | ~spl1_30)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f45,f243])).
% 0.22/0.44  fof(f243,plain,(
% 0.22/0.44    ( ! [X1] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~l1_orders_2(X1)) ) | ~spl1_30),
% 0.22/0.44    inference(avatar_component_clause,[],[f242])).
% 0.22/0.44  fof(f242,plain,(
% 0.22/0.44    spl1_30 <=> ! [X1] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~l1_orders_2(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    l1_orders_2(sK0) | ~spl1_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    spl1_1 <=> l1_orders_2(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) | spl1_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f48])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl1_2 <=> k6_yellow_1(k1_xboole_0,sK0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.44  fof(f244,plain,(
% 0.22/0.44    spl1_30 | ~spl1_12 | ~spl1_8 | ~spl1_10 | ~spl1_13 | ~spl1_17 | ~spl1_18 | ~spl1_21 | ~spl1_22 | ~spl1_23 | ~spl1_25),
% 0.22/0.44    inference(avatar_split_clause,[],[f208,f198,f171,f164,f157,f126,f121,f99,f82,f74,f94,f242])).
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    spl1_12 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl1_8 <=> ! [X0] : v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    spl1_10 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    spl1_13 <=> ! [X1,X0] : (v1_yellow_1(k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.22/0.44  fof(f121,plain,(
% 0.22/0.44    spl1_17 <=> ! [X1,X0] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.22/0.44  fof(f126,plain,(
% 0.22/0.44    spl1_18 <=> ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.22/0.44  fof(f157,plain,(
% 0.22/0.44    spl1_21 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.22/0.44  fof(f164,plain,(
% 0.22/0.44    spl1_22 <=> v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.22/0.44  fof(f171,plain,(
% 0.22/0.44    spl1_23 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.22/0.44  fof(f198,plain,(
% 0.22/0.44    spl1_25 <=> ! [X0] : k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).
% 0.22/0.44  fof(f208,plain,(
% 0.22/0.44    ( ! [X1] : (~v1_funct_1(k1_xboole_0) | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~l1_orders_2(X1)) ) | (~spl1_8 | ~spl1_10 | ~spl1_13 | ~spl1_17 | ~spl1_18 | ~spl1_21 | ~spl1_22 | ~spl1_23 | ~spl1_25)),
% 0.22/0.44    inference(subsumption_resolution,[],[f175,f204])).
% 0.22/0.44  fof(f204,plain,(
% 0.22/0.44    ( ! [X2] : (v1_yellow_1(k1_xboole_0) | ~l1_orders_2(X2)) ) | (~spl1_13 | ~spl1_25)),
% 0.22/0.44    inference(superposition,[],[f100,f199])).
% 0.22/0.44  fof(f199,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)) ) | ~spl1_25),
% 0.22/0.44    inference(avatar_component_clause,[],[f198])).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_yellow_1(k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) ) | ~spl1_13),
% 0.22/0.44    inference(avatar_component_clause,[],[f99])).
% 0.22/0.44  fof(f175,plain,(
% 0.22/0.44    ( ! [X1] : (~v1_funct_1(k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~l1_orders_2(X1)) ) | (~spl1_8 | ~spl1_10 | ~spl1_17 | ~spl1_18 | ~spl1_21 | ~spl1_22 | ~spl1_23)),
% 0.22/0.44    inference(subsumption_resolution,[],[f168,f173])).
% 0.22/0.44  fof(f173,plain,(
% 0.22/0.44    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl1_23),
% 0.22/0.44    inference(avatar_component_clause,[],[f171])).
% 0.22/0.44  fof(f168,plain,(
% 0.22/0.44    ( ! [X1] : (~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~l1_orders_2(X1)) ) | (~spl1_8 | ~spl1_10 | ~spl1_17 | ~spl1_18 | ~spl1_21 | ~spl1_22)),
% 0.22/0.44    inference(subsumption_resolution,[],[f161,f166])).
% 0.22/0.44  fof(f166,plain,(
% 0.22/0.44    v4_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_22),
% 0.22/0.44    inference(avatar_component_clause,[],[f164])).
% 0.22/0.44  fof(f161,plain,(
% 0.22/0.44    ( ! [X1] : (~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~l1_orders_2(X1)) ) | (~spl1_8 | ~spl1_10 | ~spl1_17 | ~spl1_18 | ~spl1_21)),
% 0.22/0.44    inference(subsumption_resolution,[],[f138,f159])).
% 0.22/0.44  fof(f159,plain,(
% 0.22/0.44    v1_relat_1(k1_xboole_0) | ~spl1_21),
% 0.22/0.44    inference(avatar_component_clause,[],[f157])).
% 0.22/0.44  fof(f138,plain,(
% 0.22/0.44    ( ! [X1] : (~v1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~l1_orders_2(X1)) ) | (~spl1_8 | ~spl1_10 | ~spl1_17 | ~spl1_18)),
% 0.22/0.44    inference(forward_demodulation,[],[f137,f102])).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k7_funcop_1(k1_xboole_0,X0)) ) | (~spl1_8 | ~spl1_10)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f75,f83])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl1_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f82])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ( ! [X0] : (v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))) ) | ~spl1_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f74])).
% 0.22/0.44  fof(f137,plain,(
% 0.22/0.44    ( ! [X1] : (~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | (~spl1_8 | ~spl1_10 | ~spl1_17 | ~spl1_18)),
% 0.22/0.44    inference(forward_demodulation,[],[f136,f102])).
% 0.22/0.44  fof(f136,plain,(
% 0.22/0.44    ( ! [X1] : (~v1_funct_1(k1_xboole_0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | (~spl1_8 | ~spl1_10 | ~spl1_17 | ~spl1_18)),
% 0.22/0.44    inference(forward_demodulation,[],[f135,f102])).
% 0.22/0.44  fof(f135,plain,(
% 0.22/0.44    ( ! [X1] : (~v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_yellow_1(k1_xboole_0) | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,X1)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | (~spl1_8 | ~spl1_10 | ~spl1_17 | ~spl1_18)),
% 0.22/0.44    inference(forward_demodulation,[],[f134,f102])).
% 0.22/0.44  fof(f134,plain,(
% 0.22/0.44    ( ! [X1] : (~v1_yellow_1(k1_xboole_0) | g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,X1)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | (~spl1_8 | ~spl1_10 | ~spl1_17 | ~spl1_18)),
% 0.22/0.44    inference(forward_demodulation,[],[f129,f102])).
% 0.22/0.44  fof(f129,plain,(
% 0.22/0.44    ( ! [X1] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X1) | ~v1_yellow_1(k7_funcop_1(k1_xboole_0,X1)) | ~v1_partfun1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_funct_1(k7_funcop_1(k1_xboole_0,X1)) | ~v4_relat_1(k7_funcop_1(k1_xboole_0,X1),k1_xboole_0) | ~v1_relat_1(k7_funcop_1(k1_xboole_0,X1)) | ~l1_orders_2(X1)) ) | (~spl1_17 | ~spl1_18)),
% 0.22/0.44    inference(superposition,[],[f127,f122])).
% 0.22/0.44  fof(f122,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) ) | ~spl1_17),
% 0.22/0.44    inference(avatar_component_clause,[],[f121])).
% 0.22/0.44  fof(f127,plain,(
% 0.22/0.44    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_18),
% 0.22/0.44    inference(avatar_component_clause,[],[f126])).
% 0.22/0.44  fof(f200,plain,(
% 0.22/0.44    spl1_25 | ~spl1_8 | ~spl1_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f102,f82,f74,f198])).
% 0.22/0.44  fof(f174,plain,(
% 0.22/0.44    spl1_23 | ~spl1_5 | ~spl1_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f88,f70,f61,f171])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    spl1_5 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    spl1_7 <=> ! [X0] : v1_partfun1(k6_relat_1(X0),X0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl1_5 | ~spl1_7)),
% 0.22/0.44    inference(superposition,[],[f71,f63])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f61])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    ( ! [X0] : (v1_partfun1(k6_relat_1(X0),X0)) ) | ~spl1_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f70])).
% 0.22/0.44  fof(f167,plain,(
% 0.22/0.44    spl1_22 | ~spl1_5 | ~spl1_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f87,f66,f61,f164])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    spl1_6 <=> ! [X0] : v4_relat_1(k6_relat_1(X0),X0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    v4_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_5 | ~spl1_6)),
% 0.22/0.44    inference(superposition,[],[f67,f63])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) ) | ~spl1_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f66])).
% 0.22/0.44  fof(f160,plain,(
% 0.22/0.44    spl1_21 | ~spl1_3 | ~spl1_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f86,f61,f53,f157])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl1_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    v1_relat_1(k1_xboole_0) | (~spl1_3 | ~spl1_5)),
% 0.22/0.44    inference(superposition,[],[f54,f63])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f53])).
% 0.22/0.44  fof(f128,plain,(
% 0.22/0.44    spl1_18),
% 0.22/0.44    inference(avatar_split_clause,[],[f40,f126])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f33,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0] : (k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) | (~v1_yellow_1(X0) | ~v1_partfun1(X0,k1_xboole_0) | ~v1_funct_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,axiom,(
% 0.22/0.44    ! [X0] : ((v1_yellow_1(X0) & v1_partfun1(X0,k1_xboole_0) & v1_funct_1(X0) & v4_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => k5_yellow_1(k1_xboole_0,X0) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_1)).
% 0.22/0.44  fof(f123,plain,(
% 0.22/0.44    spl1_17),
% 0.22/0.44    inference(avatar_split_clause,[],[f37,f121])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0,X1] : (k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1] : (l1_orders_2(X1) => k6_yellow_1(X0,X1) = k5_yellow_1(X0,k7_funcop_1(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_1)).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    spl1_13),
% 0.22/0.44    inference(avatar_split_clause,[],[f41,f99])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_yellow_1(k7_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f36,f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0,X1] : k7_funcop_1(X0,X1) = k2_funcop_1(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1] : (v1_yellow_1(k2_funcop_1(X0,X1)) | ~l1_orders_2(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1] : (l1_orders_2(X1) => v1_yellow_1(k2_funcop_1(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_yellow_1)).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    spl1_12 | ~spl1_4 | ~spl1_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f85,f61,f57,f94])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    spl1_4 <=> ! [X0] : v1_funct_1(k6_relat_1(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    v1_funct_1(k1_xboole_0) | (~spl1_4 | ~spl1_5)),
% 0.22/0.44    inference(superposition,[],[f58,f63])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) ) | ~spl1_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f57])).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    spl1_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f32,f82])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    spl1_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f39,f74])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0] : (v1_xboole_0(k7_funcop_1(k1_xboole_0,X0))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f25,f34])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0] : (v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0] : v1_xboole_0(k2_funcop_1(k1_xboole_0,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funcop_1)).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    spl1_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f31,f70])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (v1_partfun1(k6_relat_1(X0),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0] : (v1_partfun1(k6_relat_1(X0),X0) & v1_funct_1(k6_relat_1(X0)) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_funct_2)).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl1_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f29,f66])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    spl1_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f61])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl1_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f30,f57])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    spl1_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f28,f53])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ~spl1_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f38,f48])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    k6_yellow_1(k1_xboole_0,sK0) != g1_orders_2(k1_tarski(k1_xboole_0),k6_relat_1(k1_tarski(k1_xboole_0)))),
% 0.22/0.44    inference(forward_demodulation,[],[f23,f26])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0)) => (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,sK0) & l1_orders_2(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ? [X0] : (g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,X0) & l1_orders_2(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.22/0.44    inference(negated_conjecture,[],[f12])).
% 0.22/0.44  fof(f12,conjecture,(
% 0.22/0.44    ! [X0] : (l1_orders_2(X0) => g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) = k6_yellow_1(k1_xboole_0,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_1)).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl1_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f43])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    l1_orders_2(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (30237)------------------------------
% 0.22/0.44  % (30237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (30237)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (30237)Memory used [KB]: 6268
% 0.22/0.44  % (30237)Time elapsed: 0.049 s
% 0.22/0.44  % (30237)------------------------------
% 0.22/0.44  % (30237)------------------------------
% 0.22/0.44  % (30231)Success in time 0.081 s
%------------------------------------------------------------------------------
