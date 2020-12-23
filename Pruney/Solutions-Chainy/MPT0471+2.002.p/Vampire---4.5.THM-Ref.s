%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 112 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :  171 ( 233 expanded)
%              Number of equality atoms :   54 (  78 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f61,f65,f69,f75,f91,f96,f100,f104,f135,f165,f172,f175])).

fof(f175,plain,
    ( spl0_1
    | ~ spl0_7
    | ~ spl0_13
    | ~ spl0_22
    | ~ spl0_23 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl0_1
    | ~ spl0_7
    | ~ spl0_13
    | ~ spl0_22
    | ~ spl0_23 ),
    inference(subsumption_resolution,[],[f41,f173])).

fof(f173,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl0_7
    | ~ spl0_13
    | ~ spl0_22
    | ~ spl0_23 ),
    inference(forward_demodulation,[],[f160,f167])).

fof(f167,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl0_7
    | ~ spl0_13
    | ~ spl0_23 ),
    inference(forward_demodulation,[],[f166,f68])).

fof(f68,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl0_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl0_7
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_7])])).

fof(f166,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)
    | ~ spl0_13
    | ~ spl0_23 ),
    inference(superposition,[],[f99,f164])).

fof(f164,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl0_23 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl0_23
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_23])])).

fof(f99,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl0_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl0_13
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_13])])).

fof(f160,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl0_22 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl0_22
  <=> k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_22])])).

fof(f41,plain,
    ( k1_xboole_0 != k3_relat_1(k1_xboole_0)
    | spl0_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl0_1
  <=> k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).

fof(f172,plain,
    ( spl0_22
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_12
    | ~ spl0_14 ),
    inference(avatar_split_clause,[],[f119,f102,f93,f54,f49,f158])).

fof(f49,plain,
    ( spl0_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).

fof(f54,plain,
    ( spl0_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_4])])).

fof(f93,plain,
    ( spl0_12
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_12])])).

fof(f102,plain,
    ( spl0_14
  <=> ! [X0] :
        ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_14])])).

fof(f119,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_12
    | ~ spl0_14 ),
    inference(forward_demodulation,[],[f118,f51])).

fof(f51,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl0_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f118,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl0_4
    | ~ spl0_12
    | ~ spl0_14 ),
    inference(forward_demodulation,[],[f117,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl0_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f117,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl0_12
    | ~ spl0_14 ),
    inference(unit_resulting_resolution,[],[f95,f103])).

fof(f103,plain,
    ( ! [X0] :
        ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl0_14 ),
    inference(avatar_component_clause,[],[f102])).

fof(f95,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl0_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f165,plain,
    ( spl0_23
    | ~ spl0_7
    | ~ spl0_11
    | ~ spl0_19 ),
    inference(avatar_split_clause,[],[f141,f133,f89,f67,f163])).

fof(f89,plain,
    ( spl0_11
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_11])])).

fof(f133,plain,
    ( spl0_19
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_19])])).

fof(f141,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl0_7
    | ~ spl0_11
    | ~ spl0_19 ),
    inference(forward_demodulation,[],[f138,f68])).

fof(f138,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl0_11
    | ~ spl0_19 ),
    inference(superposition,[],[f90,f134])).

fof(f134,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl0_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f90,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl0_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f135,plain,
    ( spl0_19
    | ~ spl0_6
    | ~ spl0_8 ),
    inference(avatar_split_clause,[],[f84,f73,f63,f133])).

fof(f63,plain,
    ( spl0_6
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_6])])).

fof(f73,plain,
    ( spl0_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_8])])).

fof(f84,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl0_6
    | ~ spl0_8 ),
    inference(superposition,[],[f74,f64])).

fof(f64,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl0_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f74,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl0_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f104,plain,(
    spl0_14 ),
    inference(avatar_split_clause,[],[f28,f102])).

fof(f28,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f100,plain,(
    spl0_13 ),
    inference(avatar_split_clause,[],[f33,f98])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f96,plain,
    ( spl0_12
    | ~ spl0_2
    | ~ spl0_5 ),
    inference(avatar_split_clause,[],[f70,f59,f44,f93])).

fof(f44,plain,
    ( spl0_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).

fof(f59,plain,
    ( spl0_5
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_5])])).

fof(f70,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl0_2
    | ~ spl0_5 ),
    inference(unit_resulting_resolution,[],[f46,f60])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_relat_1(X0) )
    | ~ spl0_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f46,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl0_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f91,plain,(
    spl0_11 ),
    inference(avatar_split_clause,[],[f32,f89])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f75,plain,(
    spl0_8 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f69,plain,(
    spl0_7 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f65,plain,(
    spl0_6 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f61,plain,(
    spl0_5 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f57,plain,(
    spl0_4 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f52,plain,(
    spl0_3 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    spl0_2 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f42,plain,(
    ~ spl0_1 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f17])).

fof(f17,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:57:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.45  % (10341)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.45  % (10335)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (10330)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.45  % (10333)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (10335)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f176,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f61,f65,f69,f75,f91,f96,f100,f104,f135,f165,f172,f175])).
% 0.20/0.45  fof(f175,plain,(
% 0.20/0.45    spl0_1 | ~spl0_7 | ~spl0_13 | ~spl0_22 | ~spl0_23),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f174])).
% 0.20/0.45  fof(f174,plain,(
% 0.20/0.45    $false | (spl0_1 | ~spl0_7 | ~spl0_13 | ~spl0_22 | ~spl0_23)),
% 0.20/0.45    inference(subsumption_resolution,[],[f41,f173])).
% 0.20/0.45  fof(f173,plain,(
% 0.20/0.45    k1_xboole_0 = k3_relat_1(k1_xboole_0) | (~spl0_7 | ~spl0_13 | ~spl0_22 | ~spl0_23)),
% 0.20/0.45    inference(forward_demodulation,[],[f160,f167])).
% 0.20/0.45  fof(f167,plain,(
% 0.20/0.45    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl0_7 | ~spl0_13 | ~spl0_23)),
% 0.20/0.45    inference(forward_demodulation,[],[f166,f68])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl0_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f67])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    spl0_7 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_7])])).
% 0.20/0.45  fof(f166,plain,(
% 0.20/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)) ) | (~spl0_13 | ~spl0_23)),
% 0.20/0.45    inference(superposition,[],[f99,f164])).
% 0.20/0.45  fof(f164,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl0_23),
% 0.20/0.45    inference(avatar_component_clause,[],[f163])).
% 0.20/0.45  fof(f163,plain,(
% 0.20/0.45    spl0_23 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_23])])).
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl0_13),
% 0.20/0.45    inference(avatar_component_clause,[],[f98])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    spl0_13 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_13])])).
% 0.20/0.45  fof(f160,plain,(
% 0.20/0.45    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl0_22),
% 0.20/0.45    inference(avatar_component_clause,[],[f158])).
% 0.20/0.45  fof(f158,plain,(
% 0.20/0.45    spl0_22 <=> k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_22])])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    k1_xboole_0 != k3_relat_1(k1_xboole_0) | spl0_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    spl0_1 <=> k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).
% 0.20/0.45  fof(f172,plain,(
% 0.20/0.45    spl0_22 | ~spl0_3 | ~spl0_4 | ~spl0_12 | ~spl0_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f119,f102,f93,f54,f49,f158])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    spl0_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    spl0_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_4])])).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    spl0_12 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_12])])).
% 0.20/0.45  fof(f102,plain,(
% 0.20/0.45    spl0_14 <=> ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_14])])).
% 0.20/0.45  fof(f119,plain,(
% 0.20/0.45    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl0_3 | ~spl0_4 | ~spl0_12 | ~spl0_14)),
% 0.20/0.45    inference(forward_demodulation,[],[f118,f51])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl0_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f49])).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl0_4 | ~spl0_12 | ~spl0_14)),
% 0.20/0.45    inference(forward_demodulation,[],[f117,f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl0_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f54])).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | (~spl0_12 | ~spl0_14)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f95,f103])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl0_14),
% 0.20/0.45    inference(avatar_component_clause,[],[f102])).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    v1_relat_1(k1_xboole_0) | ~spl0_12),
% 0.20/0.45    inference(avatar_component_clause,[],[f93])).
% 0.20/0.45  fof(f165,plain,(
% 0.20/0.45    spl0_23 | ~spl0_7 | ~spl0_11 | ~spl0_19),
% 0.20/0.45    inference(avatar_split_clause,[],[f141,f133,f89,f67,f163])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    spl0_11 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_11])])).
% 0.20/0.45  fof(f133,plain,(
% 0.20/0.45    spl0_19 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_19])])).
% 0.20/0.45  fof(f141,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl0_7 | ~spl0_11 | ~spl0_19)),
% 0.20/0.45    inference(forward_demodulation,[],[f138,f68])).
% 0.20/0.45  fof(f138,plain,(
% 0.20/0.45    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) ) | (~spl0_11 | ~spl0_19)),
% 0.20/0.45    inference(superposition,[],[f90,f134])).
% 0.20/0.45  fof(f134,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl0_19),
% 0.20/0.45    inference(avatar_component_clause,[],[f133])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl0_11),
% 0.20/0.45    inference(avatar_component_clause,[],[f89])).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    spl0_19 | ~spl0_6 | ~spl0_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f84,f73,f63,f133])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    spl0_6 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_6])])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    spl0_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_8])])).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl0_6 | ~spl0_8)),
% 0.20/0.45    inference(superposition,[],[f74,f64])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl0_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f63])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl0_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f73])).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    spl0_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f28,f102])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,axiom,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    spl0_13),
% 0.20/0.45    inference(avatar_split_clause,[],[f33,f98])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    spl0_12 | ~spl0_2 | ~spl0_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f70,f59,f44,f93])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    spl0_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    spl0_5 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl0_5])])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    v1_relat_1(k1_xboole_0) | (~spl0_2 | ~spl0_5)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f46,f60])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) ) | ~spl0_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f59])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0) | ~spl0_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f44])).
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    spl0_11),
% 0.20/0.45    inference(avatar_split_clause,[],[f32,f89])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    spl0_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f29,f73])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    spl0_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f26,f67])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    spl0_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f25,f63])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    spl0_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f27,f59])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,axiom,(
% 0.20/0.45    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    spl0_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f24,f54])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,axiom,(
% 0.20/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    spl0_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f23,f49])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    spl0_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f22,f44])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ~spl0_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f21,f39])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.20/0.45    inference(flattening,[],[f17])).
% 0.20/0.45  fof(f17,negated_conjecture,(
% 0.20/0.45    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.20/0.45    inference(negated_conjecture,[],[f16])).
% 0.20/0.45  fof(f16,conjecture,(
% 0.20/0.45    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (10335)------------------------------
% 0.20/0.45  % (10335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (10335)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (10335)Memory used [KB]: 6140
% 0.20/0.45  % (10335)Time elapsed: 0.048 s
% 0.20/0.45  % (10335)------------------------------
% 0.20/0.45  % (10335)------------------------------
% 0.20/0.45  % (10329)Success in time 0.108 s
%------------------------------------------------------------------------------
