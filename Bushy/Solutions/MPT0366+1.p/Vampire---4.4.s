%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t47_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:24 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 243 expanded)
%              Number of leaves         :   38 ( 105 expanded)
%              Depth                    :    9
%              Number of atoms          :  300 ( 742 expanded)
%              Number of equality atoms :   39 (  71 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f83,f90,f97,f104,f111,f118,f127,f138,f146,f159,f166,f173,f188,f195,f202,f212,f222,f237,f245,f253,f265])).

fof(f265,plain,
    ( ~ spl5_8
    | ~ spl5_12
    | spl5_15
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f263,f96])).

fof(f96,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f263,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_12
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f262,f117])).

fof(f117,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_15
  <=> ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f262,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK3))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(resolution,[],[f230,f110])).

fof(f110,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f230,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
        | r1_tarski(sK1,k3_subset_1(X3,sK3))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X3)) )
    | ~ spl5_18 ),
    inference(resolution,[],[f58,f137])).

fof(f137,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_18
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',t43_subset_1)).

fof(f253,plain,
    ( spl5_42
    | ~ spl5_38
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f246,f243,f235,f251])).

fof(f251,plain,
    ( spl5_42
  <=> k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f235,plain,
    ( spl5_38
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f243,plain,
    ( spl5_40
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = sK4(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f246,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_38
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f244,f236])).

fof(f236,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f235])).

fof(f244,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f243])).

fof(f245,plain,
    ( spl5_40
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f213,f210,f243])).

fof(f210,plain,
    ( spl5_34
  <=> k3_subset_1(k1_xboole_0,sK4(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f213,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_34 ),
    inference(superposition,[],[f152,f211])).

fof(f211,plain,
    ( k3_subset_1(k1_xboole_0,sK4(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f210])).

fof(f152,plain,(
    ! [X2] : k3_subset_1(X2,k3_subset_1(X2,sK4(k1_zfmisc_1(X2)))) = sK4(k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f56,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',existence_m1_subset_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',involutiveness_k3_subset_1)).

fof(f237,plain,
    ( spl5_38
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f225,f220,f235])).

fof(f220,plain,
    ( spl5_36
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f225,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f223,f50])).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',t3_boole)).

fof(f223,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_36 ),
    inference(resolution,[],[f221,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',d5_subset_1)).

fof(f221,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f220])).

fof(f222,plain,
    ( spl5_36
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f215,f210,f220])).

fof(f215,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f214,f53])).

fof(f214,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK4(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_34 ),
    inference(superposition,[],[f55,f211])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',dt_k3_subset_1)).

fof(f212,plain,(
    spl5_34 ),
    inference(avatar_split_clause,[],[f204,f210])).

fof(f204,plain,(
    k3_subset_1(k1_xboole_0,sK4(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[],[f181,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',t4_boole)).

fof(f181,plain,(
    ! [X2] : k3_subset_1(X2,sK4(k1_zfmisc_1(X2))) = k4_xboole_0(X2,sK4(k1_zfmisc_1(X2))) ),
    inference(resolution,[],[f57,f53])).

fof(f202,plain,
    ( spl5_32
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f179,f109,f200])).

fof(f200,plain,
    ( spl5_32
  <=> k3_subset_1(sK0,sK3) = k4_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f179,plain,
    ( k3_subset_1(sK0,sK3) = k4_xboole_0(sK0,sK3)
    | ~ spl5_12 ),
    inference(resolution,[],[f57,f110])).

fof(f195,plain,
    ( spl5_30
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f178,f102,f193])).

fof(f193,plain,
    ( spl5_30
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f102,plain,
    ( spl5_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f178,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl5_10 ),
    inference(resolution,[],[f57,f103])).

fof(f103,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f188,plain,
    ( spl5_28
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f177,f95,f186])).

fof(f186,plain,
    ( spl5_28
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f177,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f57,f96])).

fof(f173,plain,
    ( spl5_26
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f150,f109,f171])).

fof(f171,plain,
    ( spl5_26
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f150,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK3)) = sK3
    | ~ spl5_12 ),
    inference(resolution,[],[f56,f110])).

fof(f166,plain,
    ( spl5_24
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f149,f102,f164])).

fof(f164,plain,
    ( spl5_24
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f149,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl5_10 ),
    inference(resolution,[],[f56,f103])).

fof(f159,plain,
    ( spl5_22
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f148,f95,f157])).

fof(f157,plain,
    ( spl5_22
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f148,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl5_8 ),
    inference(resolution,[],[f56,f96])).

fof(f146,plain,
    ( spl5_20
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f139,f136,f144])).

fof(f144,plain,
    ( spl5_20
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f139,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl5_18 ),
    inference(resolution,[],[f137,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',symmetry_r1_xboole_0)).

fof(f138,plain,
    ( spl5_18
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f131,f125,f74,f136])).

fof(f74,plain,
    ( spl5_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f125,plain,
    ( spl5_16
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f131,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f130,f126])).

fof(f126,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f125])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | r1_xboole_0(sK1,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f61,f75])).

fof(f75,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',t63_xboole_1)).

fof(f127,plain,
    ( spl5_16
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f120,f81,f125])).

fof(f81,plain,
    ( spl5_4
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f120,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl5_4 ),
    inference(resolution,[],[f54,f82])).

fof(f82,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f118,plain,(
    ~ spl5_15 ),
    inference(avatar_split_clause,[],[f47,f116])).

fof(f47,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    & r1_xboole_0(sK3,sK2)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
                & r1_xboole_0(X3,X2)
                & r1_tarski(X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(sK1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ? [X3] :
            ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
            & r1_xboole_0(X3,sK2)
            & r1_tarski(X1,sK2)
            & m1_subset_1(X3,k1_zfmisc_1(X0)) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
          & r1_xboole_0(X3,X2)
          & r1_tarski(X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(X1,k3_subset_1(X0,sK3))
        & r1_xboole_0(sK3,X2)
        & r1_tarski(X1,X2)
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',t47_subset_1)).

fof(f111,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f44,f109])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f43,f102])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f42,f95])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f49,f88])).

fof(f88,plain,
    ( spl5_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f49,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',d2_xboole_0)).

fof(f83,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f45,f74])).

fof(f45,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f62,f67])).

fof(f67,plain,
    ( spl5_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f48,f49])).

fof(f48,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t47_subset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
