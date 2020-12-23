%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t26_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:25 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 326 expanded)
%              Number of leaves         :   38 ( 135 expanded)
%              Depth                    :    8
%              Number of atoms          :  418 ( 904 expanded)
%              Number of equality atoms :   13 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f322,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f91,f98,f105,f112,f121,f128,f138,f148,f155,f178,f185,f206,f216,f223,f230,f243,f258,f265,f278,f285,f292,f314,f316,f318])).

fof(f318,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_9
    | spl3_35
    | spl3_37
    | ~ spl3_38 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_35
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f307,f277])).

fof(f277,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl3_38
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f307,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_35
    | ~ spl3_37 ),
    inference(backward_demodulation,[],[f294,f264])).

fof(f264,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl3_37
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f294,plain,
    ( sK0 = sK1
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_35 ),
    inference(unit_resulting_resolution,[],[f83,f257,f111,f90,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',t24_ordinal1)).

fof(f90,plain,
    ( v3_ordinal1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f111,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_9
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f257,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl3_35
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f83,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_0
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f316,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_9
    | ~ spl3_26
    | spl3_33
    | spl3_35 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_26
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f305,f215])).

fof(f215,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl3_26
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f305,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(backward_demodulation,[],[f294,f242])).

fof(f242,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl3_33
  <=> ~ r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f314,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | spl3_7
    | spl3_9
    | ~ spl3_16
    | spl3_35 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f298,f147])).

fof(f147,plain,
    ( r1_ordinal1(sK0,sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_16
  <=> r1_ordinal1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f298,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_35 ),
    inference(backward_demodulation,[],[f294,f104])).

fof(f104,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_7
  <=> ~ r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f292,plain,
    ( spl3_42
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f251,f228,f290])).

fof(f290,plain,
    ( spl3_42
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f228,plain,
    ( spl3_30
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f251,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_30 ),
    inference(unit_resulting_resolution,[],[f229,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',t3_subset)).

fof(f229,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f228])).

fof(f285,plain,
    ( spl3_40
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f232,f221,f283])).

fof(f283,plain,
    ( spl3_40
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f221,plain,
    ( spl3_28
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f232,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f222,f72])).

fof(f222,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f221])).

fof(f278,plain,
    ( spl3_38
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f231,f214,f276])).

fof(f231,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_26 ),
    inference(unit_resulting_resolution,[],[f215,f72])).

fof(f265,plain,
    ( ~ spl3_37
    | spl3_33 ),
    inference(avatar_split_clause,[],[f246,f241,f263])).

fof(f246,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | ~ spl3_33 ),
    inference(unit_resulting_resolution,[],[f242,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f258,plain,
    ( ~ spl3_35
    | ~ spl3_12
    | spl3_33 ),
    inference(avatar_split_clause,[],[f245,f241,f126,f256])).

fof(f126,plain,
    ( spl3_12
  <=> v1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f245,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl3_12
    | ~ spl3_33 ),
    inference(unit_resulting_resolution,[],[f127,f242,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',d2_ordinal1)).

fof(f127,plain,
    ( v1_ordinal1(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f243,plain,
    ( ~ spl3_33
    | ~ spl3_0
    | ~ spl3_2
    | spl3_7 ),
    inference(avatar_split_clause,[],[f235,f103,f89,f82,f241])).

fof(f235,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f83,f90,f104,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',redefinition_r1_ordinal1)).

fof(f230,plain,
    ( spl3_30
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f209,f176,f89,f82,f228])).

fof(f176,plain,
    ( spl3_20
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f209,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f90,f83,f177,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f177,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f176])).

fof(f223,plain,
    ( spl3_28
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f208,f153,f89,f221])).

fof(f153,plain,
    ( spl3_18
  <=> r1_ordinal1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f208,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f90,f90,f154,f69])).

fof(f154,plain,
    ( r1_ordinal1(sK1,sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f216,plain,
    ( spl3_26
    | ~ spl3_0
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f207,f146,f82,f214])).

fof(f207,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_0
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f83,f83,f147,f69])).

fof(f206,plain,
    ( spl3_24
    | ~ spl3_4
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f191,f183,f96,f204])).

fof(f204,plain,
    ( spl3_24
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f96,plain,
    ( spl3_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f183,plain,
    ( spl3_22
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f191,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl3_4
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f184,f131])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f129,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',t6_boole)).

fof(f129,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f97,f59])).

fof(f97,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f184,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f183])).

fof(f185,plain,
    ( spl3_22
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f166,f96,f183])).

fof(f166,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f63,f165,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',t2_subset)).

fof(f165,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f97,f63,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',t5_subset)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',existence_m1_subset_1)).

fof(f178,plain,
    ( spl3_20
    | ~ spl3_0
    | ~ spl3_2
    | spl3_7 ),
    inference(avatar_split_clause,[],[f168,f103,f89,f82,f176])).

fof(f168,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f90,f83,f104,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',connectedness_r1_ordinal1)).

fof(f155,plain,
    ( spl3_18
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f141,f89,f153])).

fof(f141,plain,
    ( r1_ordinal1(sK1,sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f90,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(condensation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',reflexivity_r1_ordinal1)).

fof(f148,plain,
    ( spl3_16
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f140,f82,f146])).

fof(f140,plain,
    ( r1_ordinal1(sK0,sK0)
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f83,f77])).

fof(f138,plain,
    ( spl3_14
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f129,f96,f136])).

fof(f136,plain,
    ( spl3_14
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f128,plain,
    ( spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f114,f89,f126])).

fof(f114,plain,
    ( v1_ordinal1(sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f90,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',cc1_ordinal1)).

fof(f121,plain,
    ( spl3_10
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f113,f82,f119])).

fof(f119,plain,
    ( spl3_10
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f113,plain,
    ( v1_ordinal1(sK0)
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f83,f60])).

fof(f112,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f57,f110])).

fof(f57,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r2_hidden(sK1,sK0)
    & ~ r1_ordinal1(sK0,sK1)
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(X1,X0)
            & ~ r1_ordinal1(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(X1,sK0)
          & ~ r1_ordinal1(sK0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(sK1,X0)
        & ~ r1_ordinal1(X0,sK1)
        & v3_ordinal1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
              | r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',t26_ordinal1)).

fof(f105,plain,(
    ~ spl3_7 ),
    inference(avatar_split_clause,[],[f56,f103])).

fof(f56,plain,(
    ~ r1_ordinal1(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f58,f96])).

fof(f58,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t26_ordinal1.p',dt_o_0_0_xboole_0)).

fof(f91,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f55,f89])).

fof(f55,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f54,f82])).

fof(f54,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
