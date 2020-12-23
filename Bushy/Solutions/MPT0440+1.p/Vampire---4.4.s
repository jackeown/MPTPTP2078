%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t23_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:00 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 563 expanded)
%              Number of leaves         :   45 ( 214 expanded)
%              Depth                    :   10
%              Number of atoms          :  561 (1411 expanded)
%              Number of equality atoms :  113 ( 436 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f67,f80,f88,f106,f130,f143,f148,f162,f166,f180,f185,f199,f203,f215,f220,f223,f229,f260,f296,f422,f522,f639,f821,f1980,f2004,f2114,f2212,f2445,f2898,f2899,f3049,f3107,f3114,f3121,f3158,f3165,f3176,f3178])).

fof(f3178,plain,
    ( ~ spl11_10
    | ~ spl11_22
    | spl11_25 ),
    inference(avatar_contradiction_clause,[],[f3177])).

fof(f3177,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_22
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f3173,f105])).

fof(f105,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl11_10
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f3173,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl11_22
    | ~ spl11_25 ),
    inference(backward_demodulation,[],[f3169,f179])).

fof(f179,plain,
    ( ~ r2_hidden(sK10(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl11_25
  <=> ~ r2_hidden(sK10(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f3169,plain,
    ( sK0 = sK10(k1_tarski(sK0),k1_relat_1(sK2))
    | ~ spl11_22 ),
    inference(resolution,[],[f170,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t23_relat_1.p',d1_tarski)).

fof(f170,plain,
    ( r2_hidden(sK10(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0))
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl11_22
  <=> r2_hidden(sK10(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f3176,plain,
    ( ~ spl11_22
    | spl11_55 ),
    inference(avatar_contradiction_clause,[],[f3175])).

fof(f3175,plain,
    ( $false
    | ~ spl11_22
    | ~ spl11_55 ),
    inference(trivial_inequality_removal,[],[f3171])).

fof(f3171,plain,
    ( k4_tarski(sK0,sK1) != k4_tarski(sK0,sK1)
    | ~ spl11_22
    | ~ spl11_55 ),
    inference(backward_demodulation,[],[f3169,f3103])).

fof(f3103,plain,
    ( k4_tarski(sK0,sK1) != k4_tarski(sK10(k1_tarski(sK0),k1_relat_1(sK2)),sK1)
    | ~ spl11_55 ),
    inference(avatar_component_clause,[],[f3102])).

fof(f3102,plain,
    ( spl11_55
  <=> k4_tarski(sK0,sK1) != k4_tarski(sK10(k1_tarski(sK0),k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_55])])).

fof(f3165,plain,
    ( ~ spl11_10
    | spl11_25
    | ~ spl11_30
    | ~ spl11_34
    | ~ spl11_54 ),
    inference(avatar_contradiction_clause,[],[f3164])).

fof(f3164,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_25
    | ~ spl11_30
    | ~ spl11_34
    | ~ spl11_54 ),
    inference(subsumption_resolution,[],[f3163,f105])).

fof(f3163,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl11_25
    | ~ spl11_30
    | ~ spl11_34
    | ~ spl11_54 ),
    inference(forward_demodulation,[],[f179,f3149])).

fof(f3149,plain,
    ( sK0 = sK10(k1_tarski(sK0),k1_relat_1(sK2))
    | ~ spl11_30
    | ~ spl11_34
    | ~ spl11_54 ),
    inference(forward_demodulation,[],[f3143,f421])).

fof(f421,plain,
    ( sK0 = sK4(sK2,sK1)
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl11_34
  <=> sK0 = sK4(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f3143,plain,
    ( sK4(sK2,sK1) = sK10(k1_tarski(sK0),k1_relat_1(sK2))
    | ~ spl11_30
    | ~ spl11_54 ),
    inference(trivial_inequality_removal,[],[f3136])).

fof(f3136,plain,
    ( k4_tarski(sK0,sK1) != k4_tarski(sK0,sK1)
    | sK4(sK2,sK1) = sK10(k1_tarski(sK0),k1_relat_1(sK2))
    | ~ spl11_30
    | ~ spl11_54 ),
    inference(superposition,[],[f269,f3106])).

fof(f3106,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK10(k1_tarski(sK0),k1_relat_1(sK2)),sK1)
    | ~ spl11_54 ),
    inference(avatar_component_clause,[],[f3105])).

fof(f3105,plain,
    ( spl11_54
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK10(k1_tarski(sK0),k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( k4_tarski(sK0,sK1) != k4_tarski(X0,X1)
        | sK4(sK2,sK1) = X0 )
    | ~ spl11_30 ),
    inference(superposition,[],[f38,f259])).

fof(f259,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK4(sK2,sK1),sK1)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl11_30
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t23_relat_1.p',t33_zfmisc_1)).

fof(f3158,plain,
    ( spl11_23
    | ~ spl11_30
    | ~ spl11_34
    | ~ spl11_54 ),
    inference(avatar_contradiction_clause,[],[f3157])).

fof(f3157,plain,
    ( $false
    | ~ spl11_23
    | ~ spl11_30
    | ~ spl11_34
    | ~ spl11_54 ),
    inference(subsumption_resolution,[],[f3150,f53])).

fof(f53,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f3150,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl11_23
    | ~ spl11_30
    | ~ spl11_34
    | ~ spl11_54 ),
    inference(backward_demodulation,[],[f3149,f173])).

fof(f173,plain,
    ( ~ r2_hidden(sK10(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0))
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl11_23
  <=> ~ r2_hidden(sK10(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f3121,plain,
    ( spl11_58
    | ~ spl11_4
    | ~ spl11_26
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f2981,f2210,f188,f69,f3119])).

fof(f3119,plain,
    ( spl11_58
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK10(k1_relat_1(sK2),k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f69,plain,
    ( spl11_4
  <=> k1_tarski(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f188,plain,
    ( spl11_26
  <=> r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f2210,plain,
    ( spl11_48
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK10(k1_relat_1(sK2),k1_tarski(sK0)),sK7(sK2,sK10(k1_relat_1(sK2),k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f2981,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK10(k1_relat_1(sK2),k1_tarski(sK0)),sK1)
    | ~ spl11_4
    | ~ spl11_26
    | ~ spl11_48 ),
    inference(backward_demodulation,[],[f2968,f2211])).

fof(f2211,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK10(k1_relat_1(sK2),k1_tarski(sK0)),sK7(sK2,sK10(k1_relat_1(sK2),k1_tarski(sK0))))
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f2210])).

fof(f2968,plain,
    ( sK1 = sK7(sK2,sK10(k1_relat_1(sK2),k1_tarski(sK0)))
    | ~ spl11_4
    | ~ spl11_26 ),
    inference(resolution,[],[f2925,f189])).

fof(f189,plain,
    ( r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_relat_1(sK2))
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f188])).

fof(f2925,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | sK1 = sK7(sK2,X1) )
    | ~ spl11_4 ),
    inference(resolution,[],[f2900,f51])).

fof(f2900,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK2,X0),k1_tarski(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl11_4 ),
    inference(superposition,[],[f108,f70])).

fof(f70,plain,
    ( k1_tarski(sK1) = k2_relat_1(sK2)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f108,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK7(X3,X2),k2_relat_1(X3))
      | ~ r2_hidden(X2,k1_relat_1(X3)) ) ),
    inference(resolution,[],[f49,f48])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t23_relat_1.p',d5_relat_1)).

fof(f49,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t23_relat_1.p',d4_relat_1)).

fof(f3114,plain,
    ( spl11_56
    | ~ spl11_4
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f2968,f188,f69,f3112])).

fof(f3112,plain,
    ( spl11_56
  <=> sK1 = sK7(sK2,sK10(k1_relat_1(sK2),k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f3107,plain,
    ( spl11_54
    | ~ spl11_4
    | ~ spl11_24
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f2979,f2112,f175,f69,f3105])).

fof(f175,plain,
    ( spl11_24
  <=> r2_hidden(sK10(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f2112,plain,
    ( spl11_46
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK10(k1_tarski(sK0),k1_relat_1(sK2)),sK7(sK2,sK10(k1_tarski(sK0),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f2979,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK10(k1_tarski(sK0),k1_relat_1(sK2)),sK1)
    | ~ spl11_4
    | ~ spl11_24
    | ~ spl11_46 ),
    inference(backward_demodulation,[],[f2966,f2113])).

fof(f2113,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK10(k1_tarski(sK0),k1_relat_1(sK2)),sK7(sK2,sK10(k1_tarski(sK0),k1_relat_1(sK2))))
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f2112])).

fof(f2966,plain,
    ( sK1 = sK7(sK2,sK10(k1_tarski(sK0),k1_relat_1(sK2)))
    | ~ spl11_4
    | ~ spl11_24 ),
    inference(resolution,[],[f2925,f176])).

fof(f176,plain,
    ( r2_hidden(sK10(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f175])).

fof(f3049,plain,
    ( spl11_52
    | ~ spl11_4
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f2966,f175,f69,f3047])).

fof(f3047,plain,
    ( spl11_52
  <=> sK1 = sK7(sK2,sK10(k1_tarski(sK0),k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f2899,plain,
    ( spl11_4
    | spl11_19
    | spl11_21 ),
    inference(avatar_split_clause,[],[f164,f160,f154,f69])).

fof(f154,plain,
    ( spl11_19
  <=> ~ r2_hidden(sK10(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f160,plain,
    ( spl11_21
  <=> ~ r2_hidden(sK10(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f164,plain,
    ( k1_tarski(sK1) = k2_relat_1(sK2)
    | ~ spl11_19
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f163,f161])).

fof(f161,plain,
    ( ~ r2_hidden(sK10(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f160])).

fof(f163,plain,
    ( r2_hidden(sK10(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2)
    | ~ spl11_19 ),
    inference(resolution,[],[f155,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X1)
      | r2_hidden(sK10(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t23_relat_1.p',t2_tarski)).

fof(f155,plain,
    ( ~ r2_hidden(sK10(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2))
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f2898,plain,
    ( ~ spl11_51
    | spl11_15
    | spl11_19
    | spl11_21 ),
    inference(avatar_split_clause,[],[f2447,f160,f154,f135,f2896])).

fof(f2896,plain,
    ( spl11_51
  <=> ~ r2_hidden(sK10(k1_tarski(sK1),k1_tarski(sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f135,plain,
    ( spl11_15
  <=> ~ r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f2447,plain,
    ( ~ r2_hidden(sK10(k1_tarski(sK1),k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl11_15
    | ~ spl11_19
    | ~ spl11_21 ),
    inference(backward_demodulation,[],[f164,f136])).

fof(f136,plain,
    ( ~ r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f2445,plain,
    ( spl11_15
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42 ),
    inference(avatar_contradiction_clause,[],[f2444])).

fof(f2444,plain,
    ( $false
    | ~ spl11_15
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f2435,f53])).

fof(f2435,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl11_15
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42 ),
    inference(backward_demodulation,[],[f2434,f136])).

fof(f2434,plain,
    ( sK1 = sK10(k1_tarski(sK1),k2_relat_1(sK2))
    | ~ spl11_36
    | ~ spl11_40
    | ~ spl11_42 ),
    inference(forward_demodulation,[],[f2414,f820])).

fof(f820,plain,
    ( sK1 = sK7(sK2,sK0)
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f819])).

fof(f819,plain,
    ( spl11_40
  <=> sK1 = sK7(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f2414,plain,
    ( sK7(sK2,sK0) = sK10(k1_tarski(sK1),k2_relat_1(sK2))
    | ~ spl11_36
    | ~ spl11_42 ),
    inference(trivial_inequality_removal,[],[f2413])).

fof(f2413,plain,
    ( k4_tarski(sK0,sK1) != k4_tarski(sK0,sK1)
    | sK7(sK2,sK0) = sK10(k1_tarski(sK1),k2_relat_1(sK2))
    | ~ spl11_36
    | ~ spl11_42 ),
    inference(superposition,[],[f569,f1979])).

fof(f1979,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK4(sK2,sK10(k1_tarski(sK1),k2_relat_1(sK2))),sK10(k1_tarski(sK1),k2_relat_1(sK2)))
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f1978])).

fof(f1978,plain,
    ( spl11_42
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK4(sK2,sK10(k1_tarski(sK1),k2_relat_1(sK2))),sK10(k1_tarski(sK1),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f569,plain,
    ( ! [X4,X5] :
        ( k4_tarski(sK0,sK1) != k4_tarski(X4,X5)
        | sK7(sK2,sK0) = X5 )
    | ~ spl11_36 ),
    inference(superposition,[],[f39,f521])).

fof(f521,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK0,sK7(sK2,sK0))
    | ~ spl11_36 ),
    inference(avatar_component_clause,[],[f520])).

fof(f520,plain,
    ( spl11_36
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK0,sK7(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2212,plain,
    ( spl11_48
    | ~ spl11_2
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f453,f188,f65,f2210])).

fof(f65,plain,
    ( spl11_2
  <=> k1_tarski(k4_tarski(sK0,sK1)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f453,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK10(k1_relat_1(sK2),k1_tarski(sK0)),sK7(sK2,sK10(k1_relat_1(sK2),k1_tarski(sK0))))
    | ~ spl11_2
    | ~ spl11_26 ),
    inference(resolution,[],[f207,f189])).

fof(f207,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | k4_tarski(sK0,sK1) = k4_tarski(X1,sK7(sK2,X1)) )
    | ~ spl11_2 ),
    inference(resolution,[],[f90,f49])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k4_tarski(sK0,sK1) = X0 )
    | ~ spl11_2 ),
    inference(superposition,[],[f51,f66])).

fof(f66,plain,
    ( k1_tarski(k4_tarski(sK0,sK1)) = sK2
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f2114,plain,
    ( spl11_46
    | ~ spl11_2
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f451,f175,f65,f2112])).

fof(f451,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK10(k1_tarski(sK0),k1_relat_1(sK2)),sK7(sK2,sK10(k1_tarski(sK0),k1_relat_1(sK2))))
    | ~ spl11_2
    | ~ spl11_24 ),
    inference(resolution,[],[f207,f176])).

fof(f2004,plain,
    ( spl11_44
    | ~ spl11_2
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f238,f151,f65,f2002])).

fof(f2002,plain,
    ( spl11_44
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK4(sK2,sK10(k2_relat_1(sK2),k1_tarski(sK1))),sK10(k2_relat_1(sK2),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f151,plain,
    ( spl11_18
  <=> r2_hidden(sK10(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f238,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK4(sK2,sK10(k2_relat_1(sK2),k1_tarski(sK1))),sK10(k2_relat_1(sK2),k1_tarski(sK1)))
    | ~ spl11_2
    | ~ spl11_18 ),
    inference(resolution,[],[f206,f152])).

fof(f152,plain,
    ( r2_hidden(sK10(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f151])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | k4_tarski(sK0,sK1) = k4_tarski(sK4(sK2,X0),X0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f90,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f1980,plain,
    ( spl11_42
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f237,f138,f65,f1978])).

fof(f138,plain,
    ( spl11_16
  <=> r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f237,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK4(sK2,sK10(k1_tarski(sK1),k2_relat_1(sK2))),sK10(k1_tarski(sK1),k2_relat_1(sK2)))
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(resolution,[],[f206,f139])).

fof(f139,plain,
    ( r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f821,plain,
    ( spl11_40
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f784,f520,f819])).

fof(f784,plain,
    ( sK1 = sK7(sK2,sK0)
    | ~ spl11_36 ),
    inference(equality_resolution,[],[f569])).

fof(f639,plain,
    ( spl11_38
    | ~ spl11_2
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f581,f520,f65,f637])).

fof(f637,plain,
    ( spl11_38
  <=> r2_hidden(sK7(sK2,sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f581,plain,
    ( r2_hidden(sK7(sK2,sK0),k2_relat_1(sK2))
    | ~ spl11_2
    | ~ spl11_36 ),
    inference(forward_demodulation,[],[f573,f66])).

fof(f573,plain,
    ( r2_hidden(sK7(sK2,sK0),k2_relat_1(k1_tarski(k4_tarski(sK0,sK1))))
    | ~ spl11_36 ),
    inference(superposition,[],[f91,f521])).

fof(f91,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_relat_1(k1_tarski(k4_tarski(X1,X0)))) ),
    inference(resolution,[],[f48,f53])).

fof(f522,plain,
    ( spl11_36
    | ~ spl11_2
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f437,f104,f65,f520])).

fof(f437,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK0,sK7(sK2,sK0))
    | ~ spl11_2
    | ~ spl11_10 ),
    inference(resolution,[],[f207,f105])).

fof(f422,plain,
    ( spl11_34
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f369,f258,f420])).

fof(f369,plain,
    ( sK0 = sK4(sK2,sK1)
    | ~ spl11_30 ),
    inference(equality_resolution,[],[f269])).

fof(f296,plain,
    ( spl11_32
    | ~ spl11_2
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f288,f258,f65,f294])).

fof(f294,plain,
    ( spl11_32
  <=> r2_hidden(sK4(sK2,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f288,plain,
    ( r2_hidden(sK4(sK2,sK1),k1_relat_1(sK2))
    | ~ spl11_2
    | ~ spl11_30 ),
    inference(forward_demodulation,[],[f286,f66])).

fof(f286,plain,
    ( r2_hidden(sK4(sK2,sK1),k1_relat_1(k1_tarski(k4_tarski(sK0,sK1))))
    | ~ spl11_30 ),
    inference(superposition,[],[f92,f259])).

fof(f92,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_relat_1(k1_tarski(k4_tarski(X0,X1)))) ),
    inference(resolution,[],[f50,f53])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f260,plain,
    ( spl11_30
    | ~ spl11_2
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f233,f128,f65,f258])).

fof(f128,plain,
    ( spl11_12
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f233,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK4(sK2,sK1),sK1)
    | ~ spl11_2
    | ~ spl11_12 ),
    inference(resolution,[],[f206,f129])).

fof(f129,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f229,plain,
    ( ~ spl11_10
    | spl11_27
    | ~ spl11_28 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_27
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f227,f105])).

fof(f227,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl11_27
    | ~ spl11_28 ),
    inference(backward_demodulation,[],[f225,f192])).

fof(f192,plain,
    ( ~ r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_relat_1(sK2))
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl11_27
  <=> ~ r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f225,plain,
    ( sK0 = sK10(k1_relat_1(sK2),k1_tarski(sK0))
    | ~ spl11_28 ),
    inference(resolution,[],[f195,f51])).

fof(f195,plain,
    ( r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl11_28
  <=> r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f223,plain,
    ( spl11_28
    | spl11_7
    | spl11_27 ),
    inference(avatar_split_clause,[],[f204,f191,f78,f194])).

fof(f78,plain,
    ( spl11_7
  <=> k1_tarski(sK0) != k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f204,plain,
    ( r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl11_7
    | ~ spl11_27 ),
    inference(subsumption_resolution,[],[f200,f79])).

fof(f79,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f200,plain,
    ( r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl11_27 ),
    inference(resolution,[],[f192,f45])).

fof(f220,plain,
    ( ~ spl11_12
    | ~ spl11_14
    | spl11_17 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f218,f129])).

fof(f218,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl11_14
    | ~ spl11_17 ),
    inference(backward_demodulation,[],[f216,f142])).

fof(f142,plain,
    ( ~ r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl11_17
  <=> ~ r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f216,plain,
    ( sK1 = sK10(k1_tarski(sK1),k2_relat_1(sK2))
    | ~ spl11_14 ),
    inference(resolution,[],[f133,f51])).

fof(f133,plain,
    ( r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl11_14
  <=> r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f215,plain,
    ( spl11_14
    | spl11_5
    | spl11_17 ),
    inference(avatar_split_clause,[],[f149,f141,f72,f132])).

fof(f72,plain,
    ( spl11_5
  <=> k1_tarski(sK1) != k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f149,plain,
    ( r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1))
    | ~ spl11_5
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f145,f73])).

fof(f73,plain,
    ( k1_tarski(sK1) != k2_relat_1(sK2)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f145,plain,
    ( r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1))
    | k1_tarski(sK1) = k2_relat_1(sK2)
    | ~ spl11_17 ),
    inference(resolution,[],[f142,f45])).

fof(f203,plain,
    ( spl11_7
    | spl11_27
    | spl11_29 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_27
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f201,f79])).

fof(f201,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl11_27
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f200,f198])).

fof(f198,plain,
    ( ~ r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl11_29
  <=> ~ r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f199,plain,
    ( ~ spl11_27
    | ~ spl11_29
    | spl11_7 ),
    inference(avatar_split_clause,[],[f116,f78,f197,f191])).

fof(f116,plain,
    ( ~ r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_tarski(sK0))
    | ~ r2_hidden(sK10(k1_relat_1(sK2),k1_tarski(sK0)),k1_relat_1(sK2))
    | ~ spl11_7 ),
    inference(extensionality_resolution,[],[f46,f79])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | ~ r2_hidden(sK10(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f185,plain,
    ( spl11_7
    | spl11_23
    | spl11_25 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_23
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f183,f79])).

fof(f183,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl11_23
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f182,f173])).

fof(f182,plain,
    ( r2_hidden(sK10(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0))
    | k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl11_25 ),
    inference(resolution,[],[f179,f45])).

fof(f180,plain,
    ( ~ spl11_23
    | ~ spl11_25
    | spl11_7 ),
    inference(avatar_split_clause,[],[f115,f78,f178,f172])).

fof(f115,plain,
    ( ~ r2_hidden(sK10(k1_tarski(sK0),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r2_hidden(sK10(k1_tarski(sK0),k1_relat_1(sK2)),k1_tarski(sK0))
    | ~ spl11_7 ),
    inference(extensionality_resolution,[],[f46,f79])).

fof(f166,plain,
    ( spl11_5
    | spl11_19
    | spl11_21 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_19
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f164,f73])).

fof(f162,plain,
    ( ~ spl11_19
    | ~ spl11_21
    | spl11_5 ),
    inference(avatar_split_clause,[],[f114,f72,f160,f154])).

fof(f114,plain,
    ( ~ r2_hidden(sK10(k2_relat_1(sK2),k1_tarski(sK1)),k1_tarski(sK1))
    | ~ r2_hidden(sK10(k2_relat_1(sK2),k1_tarski(sK1)),k2_relat_1(sK2))
    | ~ spl11_5 ),
    inference(extensionality_resolution,[],[f46,f73])).

fof(f148,plain,
    ( spl11_5
    | spl11_15
    | spl11_17 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_15
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f146,f73])).

fof(f146,plain,
    ( k1_tarski(sK1) = k2_relat_1(sK2)
    | ~ spl11_15
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f145,f136])).

fof(f143,plain,
    ( ~ spl11_15
    | ~ spl11_17
    | spl11_5 ),
    inference(avatar_split_clause,[],[f113,f72,f141,f135])).

fof(f113,plain,
    ( ~ r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ r2_hidden(sK10(k1_tarski(sK1),k2_relat_1(sK2)),k1_tarski(sK1))
    | ~ spl11_5 ),
    inference(extensionality_resolution,[],[f46,f73])).

fof(f130,plain,
    ( spl11_12
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f94,f86,f128])).

fof(f86,plain,
    ( spl11_8
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f94,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl11_8 ),
    inference(resolution,[],[f87,f48])).

fof(f87,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f106,plain,
    ( spl11_10
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f93,f86,f104])).

fof(f93,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl11_8 ),
    inference(resolution,[],[f87,f50])).

fof(f88,plain,
    ( spl11_8
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f81,f65,f86])).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl11_2 ),
    inference(superposition,[],[f53,f66])).

fof(f80,plain,
    ( ~ spl11_5
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f27,f78,f72])).

fof(f27,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | k1_tarski(sK1) != k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t23_relat_1.p',t23_relat_1)).

fof(f67,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    k1_tarski(k4_tarski(sK0,sK1)) = sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f58,plain,
    ( spl11_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
