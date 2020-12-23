%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 442 expanded)
%              Number of leaves         :   41 ( 174 expanded)
%              Depth                    :   12
%              Number of atoms          :  409 ( 917 expanded)
%              Number of equality atoms :   86 ( 317 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f90,f95,f99,f103,f110,f114,f125,f150,f155,f162,f174,f178,f185,f194,f204,f216,f230,f263,f270,f325,f335])).

fof(f335,plain,
    ( spl4_6
    | ~ spl4_9
    | ~ spl4_19
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl4_6
    | ~ spl4_9
    | ~ spl4_19
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f333,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_19
  <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f333,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0)
    | spl4_6
    | ~ spl4_9
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f332,f193])).

fof(f193,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl4_24
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f332,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,k4_xboole_0(sK0,sK0))
    | spl4_6
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f326,f94])).

fof(f94,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_6
  <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f326,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,k4_xboole_0(sK0,sK0))
    | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(superposition,[],[f324,f109])).

fof(f109,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_9
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f324,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl4_36
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f325,plain,
    ( spl4_36
    | ~ spl4_29
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f274,f268,f228,f323])).

fof(f228,plain,
    ( spl4_29
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f268,plain,
    ( spl4_33
  <=> ! [X1,X0] : k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f274,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) )
    | ~ spl4_29
    | ~ spl4_33 ),
    inference(superposition,[],[f229,f269])).

fof(f269,plain,
    ( ! [X0,X1] : k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f268])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f228])).

fof(f270,plain,
    ( spl4_33
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f266,f261,f78,f73,f68,f268])).

fof(f68,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f73,plain,
    ( spl4_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f78,plain,
    ( spl4_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f261,plain,
    ( spl4_32
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | ~ v2_funct_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f266,plain,
    ( ! [X0,X1] : k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f265,f70])).

fof(f70,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | ~ v1_relat_1(sK2) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f264,f75])).

fof(f75,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_3
    | ~ spl4_32 ),
    inference(resolution,[],[f262,f80])).

fof(f80,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f262,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_funct_1(X2)
        | k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f261])).

fof(f263,plain,(
    spl4_32 ),
    inference(avatar_split_clause,[],[f66,f261])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f65,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f62,f59])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_setfam_1(k6_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f47,f57,f57])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f230,plain,
    ( spl4_29
    | ~ spl4_8
    | ~ spl4_24
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f225,f214,f192,f101,f228])).

fof(f101,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f214,plain,
    ( spl4_27
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_8
    | ~ spl4_24
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f221,f193])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) )
    | ~ spl4_8
    | ~ spl4_27 ),
    inference(resolution,[],[f215,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( spl4_27
    | ~ spl4_22
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f205,f202,f176,f214])).

fof(f176,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f202,plain,
    ( spl4_25
  <=> ! [X1,X2] :
        ( ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_22
    | ~ spl4_25 ),
    inference(resolution,[],[f203,f177])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f176])).

fof(f203,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X1,X1) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,
    ( spl4_25
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f199,f192,f123,f112,f202])).

fof(f112,plain,
    ( spl4_10
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f123,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f199,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X1,X1) )
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f196,f113])).

fof(f113,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f196,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k4_xboole_0(X1,k1_xboole_0))
        | ~ r1_xboole_0(X1,X1) )
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(superposition,[],[f124,f193])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f194,plain,
    ( spl4_24
    | ~ spl4_10
    | ~ spl4_21
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f188,f183,f172,f112,f192])).

fof(f172,plain,
    ( spl4_21
  <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f183,plain,
    ( spl4_23
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f188,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl4_10
    | ~ spl4_21
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f186,f113])).

fof(f186,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl4_21
    | ~ spl4_23 ),
    inference(superposition,[],[f184,f173])).

fof(f173,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f172])).

fof(f184,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f183])).

fof(f185,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f59,f183])).

fof(f178,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f64,f176])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f61,f59])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f174,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f58,f172])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f162,plain,
    ( spl4_19
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f156,f153,f88,f159])).

fof(f88,plain,
    ( spl4_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f153,plain,
    ( spl4_18
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k9_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f156,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(resolution,[],[f154,f89])).

fof(f89,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k9_relat_1(sK2,X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f151,f148,f68,f153])).

fof(f148,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
        | k1_xboole_0 = k9_relat_1(sK2,X0) )
    | ~ spl4_1
    | ~ spl4_17 ),
    inference(resolution,[],[f149,f70])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f150,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f43,f148])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f125,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f63,f123])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f60,f59])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f41,f57])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f114,plain,
    ( spl4_10
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f105,f97,f88,f112])).

fof(f97,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f105,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(resolution,[],[f98,f89])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f110,plain,
    ( spl4_9
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f104,f97,f83,f107])).

fof(f83,plain,
    ( spl4_4
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f104,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(resolution,[],[f98,f85])).

fof(f85,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f103,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f45,f101])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f99,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f44,f97])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f34,f92])).

fof(f34,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

fof(f90,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f35,f88])).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f86,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f32,f83])).

fof(f32,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f33,f78])).

fof(f33,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:43:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (22602)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (22610)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (22599)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (22603)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (22602)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f341,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f90,f95,f99,f103,f110,f114,f125,f150,f155,f162,f174,f178,f185,f194,f204,f216,f230,f263,f270,f325,f335])).
% 0.20/0.46  fof(f335,plain,(
% 0.20/0.46    spl4_6 | ~spl4_9 | ~spl4_19 | ~spl4_24 | ~spl4_36),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f334])).
% 0.20/0.46  fof(f334,plain,(
% 0.20/0.46    $false | (spl4_6 | ~spl4_9 | ~spl4_19 | ~spl4_24 | ~spl4_36)),
% 0.20/0.46    inference(subsumption_resolution,[],[f333,f161])).
% 0.20/0.46  fof(f161,plain,(
% 0.20/0.46    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~spl4_19),
% 0.20/0.46    inference(avatar_component_clause,[],[f159])).
% 0.20/0.46  fof(f159,plain,(
% 0.20/0.46    spl4_19 <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.46  fof(f333,plain,(
% 0.20/0.46    k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) | (spl4_6 | ~spl4_9 | ~spl4_24 | ~spl4_36)),
% 0.20/0.46    inference(forward_demodulation,[],[f332,f193])).
% 0.20/0.46  fof(f193,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl4_24),
% 0.20/0.46    inference(avatar_component_clause,[],[f192])).
% 0.20/0.46  fof(f192,plain,(
% 0.20/0.46    spl4_24 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.46  fof(f332,plain,(
% 0.20/0.46    k1_xboole_0 != k9_relat_1(sK2,k4_xboole_0(sK0,sK0)) | (spl4_6 | ~spl4_9 | ~spl4_36)),
% 0.20/0.46    inference(subsumption_resolution,[],[f326,f94])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl4_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f92])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    spl4_6 <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.46  fof(f326,plain,(
% 0.20/0.46    k1_xboole_0 != k9_relat_1(sK2,k4_xboole_0(sK0,sK0)) | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | (~spl4_9 | ~spl4_36)),
% 0.20/0.46    inference(superposition,[],[f324,f109])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    sK0 = k4_xboole_0(sK0,sK1) | ~spl4_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f107])).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    spl4_9 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.46  fof(f324,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | ~spl4_36),
% 0.20/0.46    inference(avatar_component_clause,[],[f323])).
% 0.20/0.46  fof(f323,plain,(
% 0.20/0.46    spl4_36 <=> ! [X1,X0] : (k1_xboole_0 != k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.46  fof(f325,plain,(
% 0.20/0.46    spl4_36 | ~spl4_29 | ~spl4_33),
% 0.20/0.46    inference(avatar_split_clause,[],[f274,f268,f228,f323])).
% 0.20/0.46  fof(f228,plain,(
% 0.20/0.46    spl4_29 <=> ! [X1,X0] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.20/0.46  fof(f268,plain,(
% 0.20/0.46    spl4_33 <=> ! [X1,X0] : k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.20/0.46  fof(f274,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | (~spl4_29 | ~spl4_33)),
% 0.20/0.46    inference(superposition,[],[f229,f269])).
% 0.20/0.46  fof(f269,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl4_33),
% 0.20/0.46    inference(avatar_component_clause,[],[f268])).
% 0.20/0.46  fof(f229,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) ) | ~spl4_29),
% 0.20/0.46    inference(avatar_component_clause,[],[f228])).
% 0.20/0.46  fof(f270,plain,(
% 0.20/0.46    spl4_33 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_32),
% 0.20/0.46    inference(avatar_split_clause,[],[f266,f261,f78,f73,f68,f268])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    spl4_1 <=> v1_relat_1(sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    spl4_2 <=> v1_funct_1(sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    spl4_3 <=> v2_funct_1(sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.46  fof(f261,plain,(
% 0.20/0.46    spl4_32 <=> ! [X1,X0,X2] : (k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.46  fof(f266,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f265,f70])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    v1_relat_1(sK2) | ~spl4_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f68])).
% 0.20/0.46  fof(f265,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(sK2)) ) | (~spl4_2 | ~spl4_3 | ~spl4_32)),
% 0.20/0.46    inference(subsumption_resolution,[],[f264,f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    v1_funct_1(sK2) | ~spl4_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f73])).
% 0.20/0.46  fof(f264,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl4_3 | ~spl4_32)),
% 0.20/0.46    inference(resolution,[],[f262,f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    v2_funct_1(sK2) | ~spl4_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f78])).
% 0.20/0.46  fof(f262,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl4_32),
% 0.20/0.46    inference(avatar_component_clause,[],[f261])).
% 0.20/0.46  fof(f263,plain,(
% 0.20/0.46    spl4_32),
% 0.20/0.46    inference(avatar_split_clause,[],[f66,f261])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f65,f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f39,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f37,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f38,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f46,f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f48,f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f49,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f50,f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k9_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f62,f59])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k9_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_setfam_1(k6_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f47,f57,f57])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 0.20/0.47  fof(f230,plain,(
% 0.20/0.47    spl4_29 | ~spl4_8 | ~spl4_24 | ~spl4_27),
% 0.20/0.47    inference(avatar_split_clause,[],[f225,f214,f192,f101,f228])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl4_8 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    spl4_27 <=> ! [X1,X0] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.47  fof(f225,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) ) | (~spl4_8 | ~spl4_24 | ~spl4_27)),
% 0.20/0.47    inference(forward_demodulation,[],[f221,f193])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | (~spl4_8 | ~spl4_27)),
% 0.20/0.47    inference(resolution,[],[f215,f102])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) ) | ~spl4_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f101])).
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) ) | ~spl4_27),
% 0.20/0.47    inference(avatar_component_clause,[],[f214])).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    spl4_27 | ~spl4_22 | ~spl4_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f205,f202,f176,f214])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    spl4_22 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    spl4_25 <=> ! [X1,X2] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X1,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) ) | (~spl4_22 | ~spl4_25)),
% 0.20/0.47    inference(resolution,[],[f203,f177])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) ) | ~spl4_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f176])).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X1,X1)) ) | ~spl4_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f202])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    spl4_25 | ~spl4_10 | ~spl4_12 | ~spl4_24),
% 0.20/0.47    inference(avatar_split_clause,[],[f199,f192,f123,f112,f202])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    spl4_10 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    spl4_12 <=> ! [X1,X0,X2] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.47  fof(f199,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X1,X1)) ) | (~spl4_10 | ~spl4_12 | ~spl4_24)),
% 0.20/0.47    inference(forward_demodulation,[],[f196,f113])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f112])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_xboole_0)) | ~r1_xboole_0(X1,X1)) ) | (~spl4_12 | ~spl4_24)),
% 0.20/0.47    inference(superposition,[],[f124,f193])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) ) | ~spl4_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f123])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    spl4_24 | ~spl4_10 | ~spl4_21 | ~spl4_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f188,f183,f172,f112,f192])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    spl4_21 <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.47  fof(f183,plain,(
% 0.20/0.47    spl4_23 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl4_10 | ~spl4_21 | ~spl4_23)),
% 0.20/0.47    inference(forward_demodulation,[],[f186,f113])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ) | (~spl4_21 | ~spl4_23)),
% 0.20/0.47    inference(superposition,[],[f184,f173])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) ) | ~spl4_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f172])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) | ~spl4_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f183])).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    spl4_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f59,f183])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    spl4_22),
% 0.20/0.47    inference(avatar_split_clause,[],[f64,f176])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f61,f59])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f40,f57])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(rectify,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    spl4_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f58,f172])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f36,f57])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    spl4_19 | ~spl4_5 | ~spl4_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f156,f153,f88,f159])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    spl4_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    spl4_18 <=> ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k9_relat_1(sK2,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | (~spl4_5 | ~spl4_18)),
% 0.20/0.47    inference(resolution,[],[f154,f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f88])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k9_relat_1(sK2,X0)) ) | ~spl4_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f153])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    spl4_18 | ~spl4_1 | ~spl4_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f151,f148,f68,f153])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    spl4_17 <=> ! [X1,X0] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK2),X0) | k1_xboole_0 = k9_relat_1(sK2,X0)) ) | (~spl4_1 | ~spl4_17)),
% 0.20/0.47    inference(resolution,[],[f149,f70])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) ) | ~spl4_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f148])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    spl4_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f43,f148])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    spl4_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f63,f123])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f60,f59])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f41,f57])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    spl4_10 | ~spl4_5 | ~spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f105,f97,f88,f112])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl4_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl4_5 | ~spl4_7)),
% 0.20/0.47    inference(resolution,[],[f98,f89])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl4_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f97])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl4_9 | ~spl4_4 | ~spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f104,f97,f83,f107])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl4_4 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    sK0 = k4_xboole_0(sK0,sK1) | (~spl4_4 | ~spl4_7)),
% 0.20/0.47    inference(resolution,[],[f98,f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK1) | ~spl4_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f83])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    spl4_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f45,f101])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f44,f97])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ~spl4_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f92])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f15])).
% 0.20/0.47  fof(f15,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f88])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f83])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl4_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f78])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    v2_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f73])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f68])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (22602)------------------------------
% 0.20/0.47  % (22602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22602)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (22602)Memory used [KB]: 6268
% 0.20/0.47  % (22602)Time elapsed: 0.063 s
% 0.20/0.47  % (22602)------------------------------
% 0.20/0.47  % (22602)------------------------------
% 0.20/0.47  % (22594)Success in time 0.112 s
%------------------------------------------------------------------------------
