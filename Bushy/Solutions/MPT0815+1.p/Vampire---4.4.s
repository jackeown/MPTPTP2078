%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t8_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:12 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 276 expanded)
%              Number of leaves         :   39 ( 117 expanded)
%              Depth                    :    8
%              Number of atoms          :  312 ( 615 expanded)
%              Number of equality atoms :    9 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f78,f85,f92,f103,f110,f117,f131,f139,f146,f164,f175,f188,f195,f217,f252,f261,f268,f275,f284,f295,f310,f319,f326,f334])).

fof(f334,plain,
    ( ~ spl5_2
    | ~ spl5_4
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f331,f138])).

fof(f138,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_17
  <=> ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f331,plain,
    ( r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f286,f84])).

fof(f84,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_4
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f286,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | r2_hidden(k4_tarski(sK0,X2),k2_zfmisc_1(sK1,X3)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f63,f77])).

fof(f77,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',t106_zfmisc_1)).

fof(f326,plain,
    ( ~ spl5_49
    | spl5_45 ),
    inference(avatar_split_clause,[],[f312,f308,f324])).

fof(f324,plain,
    ( spl5_49
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f308,plain,
    ( spl5_45
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f312,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_45 ),
    inference(resolution,[],[f309,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',t1_subset)).

fof(f309,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f308])).

fof(f319,plain,
    ( ~ spl5_47
    | spl5_45 ),
    inference(avatar_split_clause,[],[f311,f308,f317])).

fof(f317,plain,
    ( spl5_47
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f311,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_45 ),
    inference(resolution,[],[f309,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',t3_subset)).

fof(f310,plain,
    ( ~ spl5_45
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f242,f215,f173,f162,f308])).

fof(f162,plain,
    ( spl5_20
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f173,plain,
    ( spl5_22
  <=> k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f215,plain,
    ( spl5_30
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f242,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f238,f174])).

fof(f174,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f173])).

fof(f238,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK4(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_20
    | ~ spl5_30 ),
    inference(resolution,[],[f165,f216])).

fof(f216,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f215])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK4(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl5_20 ),
    inference(resolution,[],[f163,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',t5_subset)).

fof(f163,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f162])).

fof(f295,plain,
    ( ~ spl5_43
    | spl5_39 ),
    inference(avatar_split_clause,[],[f277,f273,f293])).

fof(f293,plain,
    ( spl5_43
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f273,plain,
    ( spl5_39
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f277,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_39 ),
    inference(resolution,[],[f274,f52])).

fof(f274,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f273])).

fof(f284,plain,
    ( ~ spl5_41
    | spl5_39 ),
    inference(avatar_split_clause,[],[f276,f273,f282])).

fof(f282,plain,
    ( spl5_41
  <=> ~ r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f276,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_39 ),
    inference(resolution,[],[f274,f56])).

fof(f275,plain,
    ( ~ spl5_39
    | ~ spl5_4
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f244,f173,f162,f83,f273])).

fof(f244,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_4
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f240,f174])).

fof(f240,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK4(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(resolution,[],[f165,f84])).

fof(f268,plain,
    ( ~ spl5_37
    | spl5_33 ),
    inference(avatar_split_clause,[],[f254,f250,f266])).

fof(f266,plain,
    ( spl5_37
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f250,plain,
    ( spl5_33
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f254,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_33 ),
    inference(resolution,[],[f251,f52])).

fof(f251,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f250])).

fof(f261,plain,
    ( ~ spl5_35
    | spl5_33 ),
    inference(avatar_split_clause,[],[f253,f250,f259])).

fof(f259,plain,
    ( spl5_35
  <=> ~ r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f253,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl5_33 ),
    inference(resolution,[],[f251,f56])).

fof(f252,plain,
    ( ~ spl5_33
    | ~ spl5_2
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f243,f173,f162,f76,f250])).

fof(f243,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_2
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f239,f174])).

fof(f239,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK4(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(resolution,[],[f165,f77])).

fof(f217,plain,
    ( spl5_28
    | spl5_30
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f180,f173,f215,f209])).

fof(f209,plain,
    ( spl5_28
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f180,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_22 ),
    inference(superposition,[],[f147,f174])).

fof(f147,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f50,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',existence_m1_subset_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',t2_subset)).

fof(f195,plain,
    ( spl5_26
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f181,f173,f193])).

fof(f193,plain,
    ( spl5_26
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f181,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_22 ),
    inference(superposition,[],[f49,f174])).

fof(f188,plain,
    ( spl5_24
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f178,f173,f186])).

fof(f186,plain,
    ( spl5_24
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f178,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_22 ),
    inference(superposition,[],[f119,f174])).

fof(f119,plain,(
    ! [X0] : r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f55,f49])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f175,plain,
    ( spl5_22
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f168,f162,f173])).

fof(f168,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_20 ),
    inference(resolution,[],[f163,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',t6_boole)).

fof(f164,plain,
    ( spl5_20
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f157,f69,f162])).

fof(f69,plain,
    ( spl5_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f157,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_0 ),
    inference(resolution,[],[f154,f147])).

fof(f154,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_0 ),
    inference(resolution,[],[f153,f49])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f60,f70])).

fof(f70,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f69])).

fof(f146,plain,
    ( ~ spl5_19
    | spl5_13 ),
    inference(avatar_split_clause,[],[f124,f115,f144])).

fof(f144,plain,
    ( spl5_19
  <=> ~ r2_hidden(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f115,plain,
    ( spl5_13
  <=> ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f124,plain,
    ( ~ r2_hidden(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ spl5_13 ),
    inference(resolution,[],[f116,f52])).

fof(f116,plain,
    ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f139,plain,
    ( ~ spl5_17
    | spl5_15 ),
    inference(avatar_split_clause,[],[f132,f129,f137])).

fof(f129,plain,
    ( spl5_15
  <=> ~ r1_tarski(k1_tarski(k4_tarski(sK0,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f132,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ spl5_15 ),
    inference(resolution,[],[f130,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',t37_zfmisc_1)).

fof(f130,plain,
    ( ~ r1_tarski(k1_tarski(k4_tarski(sK0,sK2)),k2_zfmisc_1(sK1,sK3))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f131,plain,
    ( ~ spl5_15
    | spl5_13 ),
    inference(avatar_split_clause,[],[f123,f115,f129])).

fof(f123,plain,
    ( ~ r1_tarski(k1_tarski(k4_tarski(sK0,sK2)),k2_zfmisc_1(sK1,sK3))
    | ~ spl5_13 ),
    inference(resolution,[],[f116,f56])).

fof(f117,plain,(
    ~ spl5_13 ),
    inference(avatar_split_clause,[],[f45,f115])).

fof(f45,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        & r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(k4_tarski(sK0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r2_hidden(X2,X3)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X2,X3)
          & r2_hidden(X0,X1) )
       => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X2,X3)
        & r2_hidden(X0,X1) )
     => m1_subset_1(k1_tarski(k4_tarski(X0,X2)),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',t8_relset_1)).

fof(f110,plain,
    ( ~ spl5_11
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f96,f83,f108])).

fof(f108,plain,
    ( spl5_11
  <=> ~ r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f96,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f51,f84])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',antisymmetry_r2_hidden)).

fof(f103,plain,
    ( ~ spl5_9
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f95,f76,f101])).

fof(f101,plain,
    ( spl5_9
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f95,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f51,f77])).

fof(f92,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f47,f90])).

fof(f90,plain,
    ( spl5_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f47,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',d2_xboole_0)).

fof(f85,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f43,f76])).

fof(f43,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f64,f69])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f46,f47])).

fof(f46,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t8_relset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
