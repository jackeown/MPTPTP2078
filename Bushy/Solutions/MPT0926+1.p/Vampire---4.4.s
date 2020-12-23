%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t86_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:15 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 294 expanded)
%              Number of leaves         :   20 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  566 (1673 expanded)
%              Number of equality atoms :  257 (1126 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f77,f84,f91,f98,f105,f112,f119,f126,f133,f140,f147,f173,f191,f210,f229,f237,f255])).

fof(f255,plain,
    ( spl11_3
    | spl11_5
    | spl11_7
    | spl11_9
    | spl11_11
    | spl11_13
    | spl11_15
    | spl11_17
    | ~ spl11_18
    | ~ spl11_20
    | spl11_27 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_11
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_27 ),
    inference(subsumption_resolution,[],[f253,f249])).

fof(f249,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18
    | ~ spl11_27 ),
    inference(backward_demodulation,[],[f248,f160])).

fof(f160,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl11_27
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f248,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f247,f76])).

fof(f76,plain,
    ( k1_xboole_0 != sK0
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl11_3
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f247,plain,
    ( k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f246,f97])).

fof(f97,plain,
    ( k1_xboole_0 != sK3
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl11_9
  <=> k1_xboole_0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f246,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f245,f90])).

fof(f90,plain,
    ( k1_xboole_0 != sK2
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl11_7
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f245,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_5
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f238,f83])).

fof(f83,plain,
    ( k1_xboole_0 != sK1
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl11_5
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f238,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_18 ),
    inference(resolution,[],[f47,f132])).

fof(f132,plain,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl11_18
  <=> m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t86_mcart_1.p',t61_mcart_1)).

fof(f253,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_11
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f252,f104])).

fof(f104,plain,
    ( k1_xboole_0 != sK4
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl11_11
  <=> k1_xboole_0 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f252,plain,
    ( k1_xboole_0 = sK4
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f251,f125])).

fof(f125,plain,
    ( k1_xboole_0 != sK7
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl11_17
  <=> k1_xboole_0 != sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f251,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f250,f118])).

fof(f118,plain,
    ( k1_xboole_0 != sK6
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl11_15
  <=> k1_xboole_0 != sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f250,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_13
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f239,f111])).

fof(f111,plain,
    ( k1_xboole_0 != sK5
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl11_13
  <=> k1_xboole_0 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f239,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_20 ),
    inference(resolution,[],[f47,f139])).

fof(f139,plain,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl11_20
  <=> m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f237,plain,
    ( spl11_32
    | spl11_3
    | spl11_5
    | spl11_7
    | spl11_9
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f184,f131,f96,f89,f82,f75,f235])).

fof(f235,plain,
    ( spl11_32
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f184,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f183,f76])).

fof(f183,plain,
    ( k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f182,f97])).

fof(f182,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f181,f90])).

fof(f181,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl11_5
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f174,f83])).

fof(f174,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl11_18 ),
    inference(resolution,[],[f49,f132])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f229,plain,
    ( spl11_3
    | spl11_5
    | spl11_7
    | spl11_9
    | spl11_11
    | spl11_13
    | spl11_15
    | spl11_17
    | ~ spl11_18
    | ~ spl11_20
    | spl11_25 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_11
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f227,f223])).

fof(f223,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18
    | ~ spl11_25 ),
    inference(backward_demodulation,[],[f222,f154])).

fof(f154,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl11_25
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f222,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f221,f76])).

fof(f221,plain,
    ( k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f220,f97])).

fof(f220,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f219,f90])).

fof(f219,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_5
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f212,f83])).

fof(f212,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_18 ),
    inference(resolution,[],[f46,f132])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f227,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_11
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f226,f104])).

fof(f226,plain,
    ( k1_xboole_0 = sK4
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f225,f125])).

fof(f225,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f224,f118])).

fof(f224,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_13
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f213,f111])).

fof(f213,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl11_20 ),
    inference(resolution,[],[f46,f139])).

fof(f210,plain,
    ( spl11_3
    | spl11_5
    | spl11_7
    | spl11_9
    | spl11_11
    | spl11_13
    | spl11_15
    | spl11_17
    | ~ spl11_18
    | ~ spl11_20
    | spl11_29 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_11
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f208,f204])).

fof(f204,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18
    | ~ spl11_29 ),
    inference(backward_demodulation,[],[f203,f166])).

fof(f166,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl11_29
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f203,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f202,f76])).

fof(f202,plain,
    ( k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f201,f97])).

fof(f201,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f200,f90])).

fof(f200,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl11_5
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f193,f83])).

fof(f193,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl11_18 ),
    inference(resolution,[],[f48,f132])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f208,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl11_11
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f207,f104])).

fof(f207,plain,
    ( k1_xboole_0 = sK4
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f206,f125])).

fof(f206,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f205,f118])).

fof(f205,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl11_13
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f194,f111])).

fof(f194,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl11_20 ),
    inference(resolution,[],[f48,f139])).

fof(f191,plain,
    ( spl11_3
    | spl11_5
    | spl11_7
    | spl11_9
    | spl11_11
    | spl11_13
    | spl11_15
    | spl11_17
    | ~ spl11_18
    | ~ spl11_20
    | spl11_31 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_11
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_18
    | ~ spl11_20
    | ~ spl11_31 ),
    inference(subsumption_resolution,[],[f189,f185])).

fof(f185,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(sK8)
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9
    | ~ spl11_18
    | ~ spl11_31 ),
    inference(backward_demodulation,[],[f184,f172])).

fof(f172,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl11_31
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f189,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | ~ spl11_11
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f188,f104])).

fof(f188,plain,
    ( k1_xboole_0 = sK4
    | k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f187,f125])).

fof(f187,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f186,f118])).

fof(f186,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | ~ spl11_13
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f175,f111])).

fof(f175,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | ~ spl11_20 ),
    inference(resolution,[],[f49,f139])).

fof(f173,plain,
    ( ~ spl11_25
    | ~ spl11_27
    | ~ spl11_29
    | ~ spl11_31 ),
    inference(avatar_split_clause,[],[f63,f171,f165,f159,f153])).

fof(f63,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    inference(forward_demodulation,[],[f62,f35])).

fof(f35,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ? [X8] :
          ( ? [X9] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9)
                | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9)
                | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9)
                | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9) )
              & X8 = X9
              & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
          & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X7
      & k1_xboole_0 != X6
      & k1_xboole_0 != X5
      & k1_xboole_0 != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ~ ( ? [X8] :
              ( ? [X9] :
                  ( ~ ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                      & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                      & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                      & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
                  & X8 = X9
                  & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
              & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
          & k1_xboole_0 != X7
          & k1_xboole_0 != X6
          & k1_xboole_0 != X5
          & k1_xboole_0 != X4
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ~ ( ? [X8] :
            ( ? [X9] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                    & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                    & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                    & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
                & X8 = X9
                & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X7
        & k1_xboole_0 != X6
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t86_mcart_1.p',t86_mcart_1)).

fof(f62,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    inference(forward_demodulation,[],[f61,f35])).

fof(f61,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    inference(forward_demodulation,[],[f60,f35])).

fof(f60,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    inference(forward_demodulation,[],[f33,f35])).

fof(f33,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    inference(cnf_transformation,[],[f22])).

fof(f147,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f58,f145])).

fof(f145,plain,
    ( spl11_22
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f58,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t86_mcart_1.p',d2_xboole_0)).

fof(f140,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f59,f138])).

fof(f59,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(forward_demodulation,[],[f34,f35])).

fof(f34,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f22])).

fof(f133,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f36,f131])).

fof(f36,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f126,plain,(
    ~ spl11_17 ),
    inference(avatar_split_clause,[],[f44,f124])).

fof(f44,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f22])).

fof(f119,plain,(
    ~ spl11_15 ),
    inference(avatar_split_clause,[],[f43,f117])).

fof(f43,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f22])).

fof(f112,plain,(
    ~ spl11_13 ),
    inference(avatar_split_clause,[],[f42,f110])).

fof(f42,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,(
    ~ spl11_11 ),
    inference(avatar_split_clause,[],[f41,f103])).

fof(f41,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    ~ spl11_9 ),
    inference(avatar_split_clause,[],[f40,f96])).

fof(f40,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    ~ spl11_7 ),
    inference(avatar_split_clause,[],[f39,f89])).

fof(f39,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ~ spl11_3 ),
    inference(avatar_split_clause,[],[f37,f75])).

fof(f37,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f35,f68])).

fof(f68,plain,
    ( spl11_0
  <=> sK8 = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).
%------------------------------------------------------------------------------
