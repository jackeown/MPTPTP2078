%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 465 expanded)
%              Number of leaves         :   23 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  513 (2127 expanded)
%              Number of equality atoms :  260 (1816 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f537,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f63,f78,f84,f101,f103,f162,f256,f276,f292,f314,f321,f348,f376,f393,f464,f480,f532])).

fof(f532,plain,
    ( spl8_5
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f531])).

fof(f531,plain,
    ( $false
    | spl8_5
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f530,f30])).

fof(f30,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f530,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK6)
    | spl8_5
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f529,f30])).

fof(f529,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5),sK6)
    | spl8_5
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f53,f155])).

fof(f155,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl8_14
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f53,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_5
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f480,plain,
    ( spl8_2
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | spl8_2
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f478,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f478,plain,
    ( k1_xboole_0 = sK0
    | spl8_2
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f477,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f477,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_2
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f472,f38])).

fof(f38,plain,
    ( sK1 != sK5
    | spl8_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl8_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f472,plain,
    ( sK1 = sK5
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(superposition,[],[f24,f454])).

fof(f454,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f453,f154])).

fof(f154,plain,
    ( k1_xboole_0 != sK4
    | spl8_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f453,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | spl8_13
    | spl8_16
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f449,f150])).

fof(f150,plain,
    ( k1_xboole_0 != sK5
    | spl8_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl8_13
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f449,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | spl8_16
    | ~ spl8_22 ),
    inference(superposition,[],[f24,f444])).

fof(f444,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | spl8_16
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f443,f219])).

fof(f219,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl8_16 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl8_16
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f443,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f441,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f441,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_22 ),
    inference(superposition,[],[f387,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f387,plain,
    ( k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl8_22
  <=> k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f464,plain,
    ( spl8_1
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | spl8_1
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f462,f15])).

fof(f462,plain,
    ( k1_xboole_0 = sK0
    | spl8_1
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f461,f16])).

fof(f461,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_1
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f456,f34])).

fof(f34,plain,
    ( sK0 != sK4
    | spl8_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl8_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f456,plain,
    ( sK0 = sK4
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(superposition,[],[f23,f452])).

fof(f452,plain,
    ( sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl8_13
    | spl8_14
    | spl8_16
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f451,f154])).

fof(f451,plain,
    ( sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | spl8_13
    | spl8_16
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f448,f150])).

fof(f448,plain,
    ( sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | spl8_16
    | ~ spl8_22 ),
    inference(superposition,[],[f23,f444])).

fof(f393,plain,
    ( spl8_11
    | spl8_22
    | spl8_10
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f392,f309,f119,f385,f123])).

fof(f123,plain,
    ( spl8_11
  <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f119,plain,
    ( spl8_10
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f309,plain,
    ( spl8_20
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f392,plain,
    ( k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | spl8_10
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f332,f120])).

fof(f120,plain,
    ( k1_xboole_0 != sK6
    | spl8_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f332,plain,
    ( k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_20 ),
    inference(superposition,[],[f23,f311])).

fof(f311,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f309])).

fof(f376,plain,
    ( spl8_5
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl8_5
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f374,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f374,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),k1_xboole_0)
    | spl8_5
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f53,f121])).

fof(f121,plain,
    ( k1_xboole_0 = sK6
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f348,plain,
    ( spl8_3
    | spl8_10
    | spl8_11
    | spl8_16
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | spl8_3
    | spl8_10
    | spl8_11
    | spl8_16
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f346,f219])).

fof(f346,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | spl8_3
    | spl8_10
    | spl8_11
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f345,f17])).

fof(f345,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | spl8_3
    | spl8_10
    | spl8_11
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f340,f42])).

fof(f42,plain,
    ( sK2 != sK6
    | spl8_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl8_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f340,plain,
    ( sK2 = sK6
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | spl8_10
    | spl8_11
    | ~ spl8_20 ),
    inference(superposition,[],[f24,f338])).

% (11932)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f338,plain,
    ( sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl8_10
    | spl8_11
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f337,f124])).

fof(f124,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK4,sK5)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f337,plain,
    ( sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | spl8_10
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f333,f120])).

fof(f333,plain,
    ( sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_20 ),
    inference(superposition,[],[f24,f311])).

fof(f321,plain,
    ( spl8_9
    | ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | spl8_9
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f316,f30])).

fof(f316,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl8_9
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f72,f307])).

fof(f307,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl8_19
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f72,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl8_9
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f314,plain,
    ( spl8_19
    | spl8_20
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f313,f60,f309,f305])).

fof(f60,plain,
    ( spl8_7
  <=> k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f313,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f302,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f302,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_7 ),
    inference(superposition,[],[f23,f62])).

fof(f62,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f292,plain,
    ( spl8_5
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl8_5
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f290,f30])).

fof(f290,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK6)
    | spl8_5
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f289,f29])).

fof(f289,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6)
    | spl8_5
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f53,f151])).

fof(f151,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f276,plain,
    ( spl8_9
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl8_9
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f274,f30])).

fof(f274,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl8_9
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f273,f30])).

fof(f273,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | spl8_9
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f72,f220])).

fof(f220,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f218])).

fof(f256,plain,(
    ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f254,f16])).

fof(f254,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f246,f15])).

fof(f246,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl8_9 ),
    inference(trivial_inequality_removal,[],[f245])).

fof(f245,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl8_9 ),
    inference(superposition,[],[f20,f232])).

fof(f232,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f215,f17])).

fof(f215,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl8_9 ),
    inference(trivial_inequality_removal,[],[f214])).

fof(f214,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl8_9 ),
    inference(superposition,[],[f20,f190])).

fof(f190,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f137,f18])).

fof(f137,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK3
    | ~ spl8_9 ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK3
    | ~ spl8_9 ),
    inference(superposition,[],[f20,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f162,plain,
    ( spl8_13
    | spl8_14
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f145,f123,f153,f149])).

fof(f145,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK5
    | ~ spl8_11 ),
    inference(trivial_inequality_removal,[],[f144])).

fof(f144,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK5
    | ~ spl8_11 ),
    inference(superposition,[],[f20,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f103,plain,
    ( spl8_5
    | spl8_8
    | spl8_6 ),
    inference(avatar_split_clause,[],[f102,f56,f65,f52])).

fof(f65,plain,
    ( spl8_8
  <=> sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f56,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f102,plain,
    ( sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | spl8_6 ),
    inference(subsumption_resolution,[],[f86,f57])).

fof(f57,plain,
    ( k1_xboole_0 != sK7
    | spl8_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f86,plain,
    ( sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    inference(superposition,[],[f24,f28])).

fof(f28,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f14,f27,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f14,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f11])).

fof(f101,plain,
    ( spl8_4
    | ~ spl8_8
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl8_4
    | ~ spl8_8
    | spl8_9 ),
    inference(subsumption_resolution,[],[f95,f30])).

fof(f95,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl8_4
    | ~ spl8_8
    | spl8_9 ),
    inference(backward_demodulation,[],[f72,f91])).

fof(f91,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f90,f18])).

fof(f90,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f88,f46])).

fof(f46,plain,
    ( sK3 != sK7
    | spl8_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl8_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f88,plain,
    ( sK3 = sK7
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_8 ),
    inference(superposition,[],[f67,f24])).

fof(f67,plain,
    ( sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f84,plain,
    ( ~ spl8_6
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl8_6
    | spl8_9 ),
    inference(subsumption_resolution,[],[f82,f72])).

fof(f82,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f79,f29])).

fof(f79,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f28,f58])).

fof(f58,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f78,plain,
    ( ~ spl8_5
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl8_5
    | spl8_9 ),
    inference(subsumption_resolution,[],[f76,f72])).

fof(f76,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f75,f30])).

fof(f75,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f28,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f63,plain,
    ( spl8_5
    | spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f48,f60,f56,f52])).

fof(f48,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    inference(superposition,[],[f23,f28])).

fof(f47,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f19,f44,f40,f36,f32])).

fof(f19,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (11920)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (11913)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (11916)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (11930)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (11917)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (11940)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (11914)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11922)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (11919)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (11915)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (11928)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (11920)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f537,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f47,f63,f78,f84,f101,f103,f162,f256,f276,f292,f314,f321,f348,f376,f393,f464,f480,f532])).
% 0.21/0.52  fof(f532,plain,(
% 0.21/0.52    spl8_5 | ~spl8_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f531])).
% 0.21/0.52  fof(f531,plain,(
% 0.21/0.52    $false | (spl8_5 | ~spl8_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f530,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f530,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK6) | (spl8_5 | ~spl8_14)),
% 0.21/0.52    inference(forward_demodulation,[],[f529,f30])).
% 0.21/0.52  fof(f529,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5),sK6) | (spl8_5 | ~spl8_14)),
% 0.21/0.52    inference(forward_demodulation,[],[f53,f155])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    k1_xboole_0 = sK4 | ~spl8_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl8_14 <=> k1_xboole_0 = sK4),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | spl8_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    spl8_5 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.52  fof(f480,plain,(
% 0.21/0.52    spl8_2 | spl8_13 | spl8_14 | spl8_16 | ~spl8_22),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f479])).
% 0.21/0.52  fof(f479,plain,(
% 0.21/0.52    $false | (spl8_2 | spl8_13 | spl8_14 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f478,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.52    inference(flattening,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).
% 0.21/0.52  fof(f478,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | (spl8_2 | spl8_13 | spl8_14 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f477,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f477,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl8_2 | spl8_13 | spl8_14 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f472,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    sK1 != sK5 | spl8_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    spl8_2 <=> sK1 = sK5),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.52  fof(f472,plain,(
% 0.21/0.52    sK1 = sK5 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl8_13 | spl8_14 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(superposition,[],[f24,f454])).
% 0.21/0.52  fof(f454,plain,(
% 0.21/0.52    sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | (spl8_13 | spl8_14 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f453,f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    k1_xboole_0 != sK4 | spl8_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f153])).
% 0.21/0.52  fof(f453,plain,(
% 0.21/0.52    sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | (spl8_13 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f449,f150])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    k1_xboole_0 != sK5 | spl8_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl8_13 <=> k1_xboole_0 = sK5),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.52  fof(f449,plain,(
% 0.21/0.52    sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | (spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(superposition,[],[f24,f444])).
% 0.21/0.52  fof(f444,plain,(
% 0.21/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | (spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f443,f219])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl8_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f218])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    spl8_16 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.52  fof(f443,plain,(
% 0.21/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_22),
% 0.21/0.52    inference(subsumption_resolution,[],[f441,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    k1_xboole_0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f441,plain,(
% 0.21/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_22),
% 0.21/0.52    inference(superposition,[],[f387,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.52  fof(f387,plain,(
% 0.21/0.52    k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f385])).
% 0.21/0.52  fof(f385,plain,(
% 0.21/0.52    spl8_22 <=> k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f464,plain,(
% 0.21/0.52    spl8_1 | spl8_13 | spl8_14 | spl8_16 | ~spl8_22),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f463])).
% 0.21/0.52  fof(f463,plain,(
% 0.21/0.52    $false | (spl8_1 | spl8_13 | spl8_14 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f462,f15])).
% 0.21/0.52  fof(f462,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | (spl8_1 | spl8_13 | spl8_14 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f461,f16])).
% 0.21/0.52  fof(f461,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl8_1 | spl8_13 | spl8_14 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f456,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    sK0 != sK4 | spl8_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    spl8_1 <=> sK0 = sK4),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.52  fof(f456,plain,(
% 0.21/0.52    sK0 = sK4 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl8_13 | spl8_14 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(superposition,[],[f23,f452])).
% 0.21/0.52  fof(f452,plain,(
% 0.21/0.52    sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | (spl8_13 | spl8_14 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f451,f154])).
% 0.21/0.52  fof(f451,plain,(
% 0.21/0.52    sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | (spl8_13 | spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f448,f150])).
% 0.21/0.52  fof(f448,plain,(
% 0.21/0.52    sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | (spl8_16 | ~spl8_22)),
% 0.21/0.52    inference(superposition,[],[f23,f444])).
% 0.21/0.52  fof(f393,plain,(
% 0.21/0.52    spl8_11 | spl8_22 | spl8_10 | ~spl8_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f392,f309,f119,f385,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    spl8_11 <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    spl8_10 <=> k1_xboole_0 = sK6),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    spl8_20 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.52  fof(f392,plain,(
% 0.21/0.52    k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | (spl8_10 | ~spl8_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f332,f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    k1_xboole_0 != sK6 | spl8_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f119])).
% 0.21/0.52  fof(f332,plain,(
% 0.21/0.52    k2_zfmisc_1(sK4,sK5) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl8_20),
% 0.21/0.52    inference(superposition,[],[f23,f311])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl8_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f309])).
% 0.21/0.52  fof(f376,plain,(
% 0.21/0.52    spl8_5 | ~spl8_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f375])).
% 0.21/0.52  fof(f375,plain,(
% 0.21/0.52    $false | (spl8_5 | ~spl8_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f374,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f374,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),k1_xboole_0) | (spl8_5 | ~spl8_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f53,f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    k1_xboole_0 = sK6 | ~spl8_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f119])).
% 0.21/0.52  fof(f348,plain,(
% 0.21/0.52    spl8_3 | spl8_10 | spl8_11 | spl8_16 | ~spl8_20),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f347])).
% 0.21/0.52  fof(f347,plain,(
% 0.21/0.52    $false | (spl8_3 | spl8_10 | spl8_11 | spl8_16 | ~spl8_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f346,f219])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (spl8_3 | spl8_10 | spl8_11 | ~spl8_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f345,f17])).
% 0.21/0.52  fof(f345,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (spl8_3 | spl8_10 | spl8_11 | ~spl8_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f340,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    sK2 != sK6 | spl8_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    spl8_3 <=> sK2 = sK6),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.52  fof(f340,plain,(
% 0.21/0.52    sK2 = sK6 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (spl8_10 | spl8_11 | ~spl8_20)),
% 0.21/0.52    inference(superposition,[],[f24,f338])).
% 0.21/0.52  % (11932)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  fof(f338,plain,(
% 0.21/0.52    sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | (spl8_10 | spl8_11 | ~spl8_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f337,f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(sK4,sK5) | spl8_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f123])).
% 0.21/0.52  fof(f337,plain,(
% 0.21/0.52    sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | (spl8_10 | ~spl8_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f333,f120])).
% 0.21/0.52  fof(f333,plain,(
% 0.21/0.52    sK6 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl8_20),
% 0.21/0.52    inference(superposition,[],[f24,f311])).
% 0.21/0.52  fof(f321,plain,(
% 0.21/0.52    spl8_9 | ~spl8_19),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f320])).
% 0.21/0.52  fof(f320,plain,(
% 0.21/0.52    $false | (spl8_9 | ~spl8_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f316,f30])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (spl8_9 | ~spl8_19)),
% 0.21/0.52    inference(backward_demodulation,[],[f72,f307])).
% 0.21/0.52  fof(f307,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f305])).
% 0.21/0.52  fof(f305,plain,(
% 0.21/0.52    spl8_19 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | spl8_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl8_9 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.52  fof(f314,plain,(
% 0.21/0.52    spl8_19 | spl8_20 | ~spl8_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f313,f60,f309,f305])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    spl8_7 <=> k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_7),
% 0.21/0.52    inference(subsumption_resolution,[],[f302,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k1_xboole_0 != sK3),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f302,plain,(
% 0.21/0.52    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_7),
% 0.21/0.52    inference(superposition,[],[f23,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl8_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f60])).
% 0.21/0.52  fof(f292,plain,(
% 0.21/0.52    spl8_5 | ~spl8_13),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f291])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    $false | (spl8_5 | ~spl8_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f290,f30])).
% 0.21/0.52  fof(f290,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK6) | (spl8_5 | ~spl8_13)),
% 0.21/0.52    inference(forward_demodulation,[],[f289,f29])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6) | (spl8_5 | ~spl8_13)),
% 0.21/0.52    inference(forward_demodulation,[],[f53,f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    k1_xboole_0 = sK5 | ~spl8_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f149])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    spl8_9 | ~spl8_16),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    $false | (spl8_9 | ~spl8_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f274,f30])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (spl8_9 | ~spl8_16)),
% 0.21/0.52    inference(forward_demodulation,[],[f273,f30])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | (spl8_9 | ~spl8_16)),
% 0.21/0.52    inference(forward_demodulation,[],[f72,f220])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f218])).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    ~spl8_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f255])).
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    $false | ~spl8_9),
% 0.21/0.52    inference(subsumption_resolution,[],[f254,f16])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl8_9),
% 0.21/0.52    inference(subsumption_resolution,[],[f246,f15])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl8_9),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f245])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl8_9),
% 0.21/0.52    inference(superposition,[],[f20,f232])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_9),
% 0.21/0.52    inference(subsumption_resolution,[],[f215,f17])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl8_9),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f214])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl8_9),
% 0.21/0.52    inference(superposition,[],[f20,f190])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_9),
% 0.21/0.52    inference(subsumption_resolution,[],[f137,f18])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK3 | ~spl8_9),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f136])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = sK3 | ~spl8_9),
% 0.21/0.52    inference(superposition,[],[f20,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl8_13 | spl8_14 | ~spl8_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f145,f123,f153,f149])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    k1_xboole_0 = sK4 | k1_xboole_0 = sK5 | ~spl8_11),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f144])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 = sK5 | ~spl8_11),
% 0.21/0.52    inference(superposition,[],[f20,f125])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl8_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f123])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl8_5 | spl8_8 | spl8_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f102,f56,f65,f52])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl8_8 <=> sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    spl8_6 <=> k1_xboole_0 = sK7),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | spl8_6),
% 0.21/0.52    inference(subsumption_resolution,[],[f86,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    k1_xboole_0 != sK7 | spl8_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f56])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 0.21/0.52    inference(superposition,[],[f24,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 0.21/0.52    inference(definition_unfolding,[],[f14,f27,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl8_4 | ~spl8_8 | spl8_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    $false | (spl8_4 | ~spl8_8 | spl8_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f95,f30])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (spl8_4 | ~spl8_8 | spl8_9)),
% 0.21/0.52    inference(backward_demodulation,[],[f72,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (spl8_4 | ~spl8_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f90,f18])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (spl8_4 | ~spl8_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f88,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    sK3 != sK7 | spl8_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    spl8_4 <=> sK3 = sK7),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    sK3 = sK7 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_8),
% 0.21/0.52    inference(superposition,[],[f67,f24])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl8_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~spl8_6 | spl8_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    $false | (~spl8_6 | spl8_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f82,f72])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_6),
% 0.21/0.52    inference(forward_demodulation,[],[f79,f29])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_xboole_0) | ~spl8_6),
% 0.21/0.52    inference(backward_demodulation,[],[f28,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    k1_xboole_0 = sK7 | ~spl8_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f56])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ~spl8_5 | spl8_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    $false | (~spl8_5 | spl8_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f76,f72])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_5),
% 0.21/0.52    inference(forward_demodulation,[],[f75,f30])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) | ~spl8_5),
% 0.21/0.52    inference(backward_demodulation,[],[f28,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl8_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f52])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl8_5 | spl8_6 | spl8_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f48,f60,f56,f52])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 0.21/0.52    inference(superposition,[],[f23,f28])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f19,f44,f40,f36,f32])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (11920)------------------------------
% 0.21/0.52  % (11920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11920)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (11920)Memory used [KB]: 10874
% 0.21/0.52  % (11920)Time elapsed: 0.104 s
% 0.21/0.52  % (11920)------------------------------
% 0.21/0.52  % (11920)------------------------------
% 0.21/0.52  % (11911)Success in time 0.166 s
%------------------------------------------------------------------------------
