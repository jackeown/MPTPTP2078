%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 187 expanded)
%              Number of leaves         :   26 (  86 expanded)
%              Depth                    :    8
%              Number of atoms          :  279 ( 529 expanded)
%              Number of equality atoms :   71 ( 145 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (25977)Termination reason: Refutation not found, incomplete strategy

% (25977)Memory used [KB]: 10618
% (25977)Time elapsed: 0.115 s
% (25977)------------------------------
% (25977)------------------------------
fof(f420,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f84,f116,f131,f167,f174,f241,f290,f311,f377,f388,f409,f418,f419])).

fof(f419,plain,
    ( k2_funct_1(sK0) != k4_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f418,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | ~ spl1_43
    | ~ spl1_11
    | spl1_34 ),
    inference(avatar_split_clause,[],[f417,f308,f113,f406,f81,f74])).

fof(f74,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f81,plain,
    ( spl1_6
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f406,plain,
    ( spl1_43
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_43])])).

fof(f113,plain,
    ( spl1_11
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f308,plain,
    ( spl1_34
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_34])])).

fof(f417,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_11
    | spl1_34 ),
    inference(forward_demodulation,[],[f414,f115])).

fof(f115,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f414,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_34 ),
    inference(trivial_inequality_removal,[],[f412])).

fof(f412,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_34 ),
    inference(superposition,[],[f310,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f310,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_34 ),
    inference(avatar_component_clause,[],[f308])).

fof(f409,plain,
    ( spl1_43
    | ~ spl1_26
    | ~ spl1_39 ),
    inference(avatar_split_clause,[],[f404,f374,f238,f406])).

fof(f238,plain,
    ( spl1_26
  <=> r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).

fof(f374,plain,
    ( spl1_39
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_39])])).

fof(f404,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_26
    | ~ spl1_39 ),
    inference(backward_demodulation,[],[f240,f376])).

fof(f376,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ spl1_39 ),
    inference(avatar_component_clause,[],[f374])).

fof(f240,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)),k2_relat_1(sK0))
    | ~ spl1_26 ),
    inference(avatar_component_clause,[],[f238])).

fof(f388,plain,
    ( spl1_40
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f383,f164,f81,f74,f385])).

fof(f385,plain,
    ( spl1_40
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_40])])).

fof(f164,plain,
    ( spl1_17
  <=> k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f383,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_17 ),
    inference(forward_demodulation,[],[f351,f166])).

fof(f166,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f164])).

fof(f351,plain,
    ( k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f76,f83,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f83,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f81])).

% (25976)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% (25981)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (25986)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% (25989)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (25984)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (25980)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% (25972)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
fof(f76,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f377,plain,
    ( spl1_39
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_13
    | ~ spl1_18 ),
    inference(avatar_split_clause,[],[f372,f171,f128,f81,f74,f374])).

fof(f128,plain,
    ( spl1_13
  <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f171,plain,
    ( spl1_18
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f372,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_13
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f371,f173])).

fof(f173,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f371,plain,
    ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f355,f130])).

fof(f130,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f355,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0)))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f83,f76,f40])).

fof(f311,plain,
    ( ~ spl1_34
    | spl1_1
    | ~ spl1_33 ),
    inference(avatar_split_clause,[],[f292,f286,f55,f308])).

fof(f55,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f286,plain,
    ( spl1_33
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).

fof(f292,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_1
    | ~ spl1_33 ),
    inference(backward_demodulation,[],[f57,f288])).

fof(f288,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_33 ),
    inference(avatar_component_clause,[],[f286])).

fof(f57,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f290,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_33
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f283,f64,f286,f69,f74])).

fof(f69,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f64,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f283,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f48,f66])).

fof(f66,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f241,plain,
    ( spl1_26
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f219,f81,f74,f238])).

fof(f219,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)),k2_relat_1(sK0))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f83,f76,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f174,plain,
    ( spl1_18
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f156,f74,f171])).

fof(f156,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f76,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f167,plain,
    ( spl1_17
    | ~ spl1_6
    | ~ spl1_11
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f162,f128,f113,f81,f164])).

fof(f162,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_6
    | ~ spl1_11
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f161,f130])).

fof(f161,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f158,f115])).

fof(f158,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f83,f45])).

fof(f131,plain,
    ( spl1_13
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f117,f74,f128])).

fof(f117,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f76,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f116,plain,
    ( spl1_11
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f103,f74,f113])).

fof(f103,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f76,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,
    ( spl1_6
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f78,f74,f81])).

fof(f78,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f76,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f77,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f72,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f35,f64])).

fof(f35,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f36,f59,f55])).

fof(f59,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f36,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:39:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (25971)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.51  % (25974)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (25969)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (25974)Refutation not found, incomplete strategy% (25974)------------------------------
% 0.20/0.51  % (25974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25974)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (25974)Memory used [KB]: 6140
% 0.20/0.51  % (25974)Time elapsed: 0.095 s
% 0.20/0.51  % (25974)------------------------------
% 0.20/0.51  % (25974)------------------------------
% 0.20/0.51  % (25967)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (25990)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (25985)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (25968)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (25970)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.52  % (25987)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.52  % (25970)Refutation not found, incomplete strategy% (25970)------------------------------
% 0.20/0.52  % (25970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25970)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25970)Memory used [KB]: 10618
% 0.20/0.52  % (25970)Time elapsed: 0.101 s
% 0.20/0.52  % (25970)------------------------------
% 0.20/0.52  % (25970)------------------------------
% 0.20/0.52  % (25975)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  % (25991)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.52  % (25991)Refutation not found, incomplete strategy% (25991)------------------------------
% 0.20/0.52  % (25991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25991)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25991)Memory used [KB]: 10618
% 0.20/0.52  % (25991)Time elapsed: 0.107 s
% 0.20/0.52  % (25991)------------------------------
% 0.20/0.52  % (25991)------------------------------
% 0.20/0.52  % (25973)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.52  % (25978)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.52  % (25977)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.52  % (25983)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.52  % (25977)Refutation not found, incomplete strategy% (25977)------------------------------
% 0.20/0.52  % (25977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25973)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  % (25977)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25977)Memory used [KB]: 10618
% 0.20/0.53  % (25977)Time elapsed: 0.115 s
% 0.20/0.53  % (25977)------------------------------
% 0.20/0.53  % (25977)------------------------------
% 0.20/0.53  fof(f420,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f84,f116,f131,f167,f174,f241,f290,f311,f377,f388,f409,f418,f419])).
% 0.20/0.53  fof(f419,plain,(
% 0.20/0.53    k2_funct_1(sK0) != k4_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f418,plain,(
% 0.20/0.53    ~spl1_5 | ~spl1_6 | ~spl1_43 | ~spl1_11 | spl1_34),
% 0.20/0.53    inference(avatar_split_clause,[],[f417,f308,f113,f406,f81,f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    spl1_5 <=> v1_relat_1(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    spl1_6 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.53  fof(f406,plain,(
% 0.20/0.53    spl1_43 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_43])])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    spl1_11 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.53  fof(f308,plain,(
% 0.20/0.53    spl1_34 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_34])])).
% 0.20/0.53  fof(f417,plain,(
% 0.20/0.53    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_11 | spl1_34)),
% 0.20/0.53    inference(forward_demodulation,[],[f414,f115])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f113])).
% 0.20/0.53  fof(f414,plain,(
% 0.20/0.53    ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_34),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f412])).
% 0.20/0.53  fof(f412,plain,(
% 0.20/0.53    k1_relat_1(sK0) != k1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_34),
% 0.20/0.53    inference(superposition,[],[f310,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.53  fof(f310,plain,(
% 0.20/0.53    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | spl1_34),
% 0.20/0.53    inference(avatar_component_clause,[],[f308])).
% 0.20/0.53  fof(f409,plain,(
% 0.20/0.53    spl1_43 | ~spl1_26 | ~spl1_39),
% 0.20/0.53    inference(avatar_split_clause,[],[f404,f374,f238,f406])).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    spl1_26 <=> r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)),k2_relat_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).
% 0.20/0.53  fof(f374,plain,(
% 0.20/0.53    spl1_39 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_39])])).
% 0.20/0.53  fof(f404,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | (~spl1_26 | ~spl1_39)),
% 0.20/0.53    inference(backward_demodulation,[],[f240,f376])).
% 0.20/0.53  fof(f376,plain,(
% 0.20/0.53    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | ~spl1_39),
% 0.20/0.53    inference(avatar_component_clause,[],[f374])).
% 0.20/0.53  fof(f240,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)),k2_relat_1(sK0)) | ~spl1_26),
% 0.20/0.53    inference(avatar_component_clause,[],[f238])).
% 0.20/0.53  fof(f388,plain,(
% 0.20/0.53    spl1_40 | ~spl1_5 | ~spl1_6 | ~spl1_17),
% 0.20/0.53    inference(avatar_split_clause,[],[f383,f164,f81,f74,f385])).
% 0.20/0.53  fof(f385,plain,(
% 0.20/0.53    spl1_40 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_40])])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    spl1_17 <=> k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.20/0.53  fof(f383,plain,(
% 0.20/0.53    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (~spl1_5 | ~spl1_6 | ~spl1_17)),
% 0.20/0.53    inference(forward_demodulation,[],[f351,f166])).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f164])).
% 0.20/0.53  fof(f351,plain,(
% 0.20/0.53    k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (~spl1_5 | ~spl1_6)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f76,f83,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    v1_relat_1(k4_relat_1(sK0)) | ~spl1_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f81])).
% 0.20/0.53  % (25976)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.53  % (25981)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.53  % (25986)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.53  % (25989)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.53  % (25984)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.53  % (25980)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.54  % (25972)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    v1_relat_1(sK0) | ~spl1_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f74])).
% 0.20/0.54  fof(f377,plain,(
% 0.20/0.54    spl1_39 | ~spl1_5 | ~spl1_6 | ~spl1_13 | ~spl1_18),
% 0.20/0.54    inference(avatar_split_clause,[],[f372,f171,f128,f81,f74,f374])).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    spl1_13 <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.54  fof(f171,plain,(
% 0.20/0.54    spl1_18 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.20/0.54  fof(f372,plain,(
% 0.20/0.54    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_13 | ~spl1_18)),
% 0.20/0.54    inference(forward_demodulation,[],[f371,f173])).
% 0.20/0.54  fof(f173,plain,(
% 0.20/0.54    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f171])).
% 0.20/0.54  fof(f371,plain,(
% 0.20/0.54    k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_13)),
% 0.20/0.54    inference(forward_demodulation,[],[f355,f130])).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_13),
% 0.20/0.54    inference(avatar_component_clause,[],[f128])).
% 0.20/0.54  fof(f355,plain,(
% 0.20/0.54    k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0))) | (~spl1_5 | ~spl1_6)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f83,f76,f40])).
% 0.20/0.54  fof(f311,plain,(
% 0.20/0.54    ~spl1_34 | spl1_1 | ~spl1_33),
% 0.20/0.54    inference(avatar_split_clause,[],[f292,f286,f55,f308])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    spl1_1 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.54  fof(f286,plain,(
% 0.20/0.54    spl1_33 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).
% 0.20/0.54  fof(f292,plain,(
% 0.20/0.54    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (spl1_1 | ~spl1_33)),
% 0.20/0.54    inference(backward_demodulation,[],[f57,f288])).
% 0.20/0.54  fof(f288,plain,(
% 0.20/0.54    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_33),
% 0.20/0.54    inference(avatar_component_clause,[],[f286])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f55])).
% 0.20/0.54  fof(f290,plain,(
% 0.20/0.54    ~spl1_5 | ~spl1_4 | spl1_33 | ~spl1_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f283,f64,f286,f69,f74])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    spl1_4 <=> v1_funct_1(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    spl1_3 <=> v2_funct_1(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.54  fof(f283,plain,(
% 0.20/0.54    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.20/0.54    inference(resolution,[],[f48,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    v2_funct_1(sK0) | ~spl1_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f64])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.54  fof(f241,plain,(
% 0.20/0.54    spl1_26 | ~spl1_5 | ~spl1_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f219,f81,f74,f238])).
% 0.20/0.54  fof(f219,plain,(
% 0.20/0.54    r1_tarski(k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)),k2_relat_1(sK0)) | (~spl1_5 | ~spl1_6)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f83,f76,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.20/0.54  fof(f174,plain,(
% 0.20/0.54    spl1_18 | ~spl1_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f156,f74,f171])).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_5),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f76,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.54  fof(f167,plain,(
% 0.20/0.54    spl1_17 | ~spl1_6 | ~spl1_11 | ~spl1_13),
% 0.20/0.54    inference(avatar_split_clause,[],[f162,f128,f113,f81,f164])).
% 0.20/0.54  fof(f162,plain,(
% 0.20/0.54    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | (~spl1_6 | ~spl1_11 | ~spl1_13)),
% 0.20/0.54    inference(forward_demodulation,[],[f161,f130])).
% 0.20/0.54  fof(f161,plain,(
% 0.20/0.54    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | (~spl1_6 | ~spl1_11)),
% 0.20/0.54    inference(forward_demodulation,[],[f158,f115])).
% 0.20/0.54  fof(f158,plain,(
% 0.20/0.54    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | ~spl1_6),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f83,f45])).
% 0.20/0.54  fof(f131,plain,(
% 0.20/0.54    spl1_13 | ~spl1_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f117,f74,f128])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f76,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    spl1_11 | ~spl1_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f103,f74,f113])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f76,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    spl1_6 | ~spl1_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f78,f74,f81])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    v1_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f76,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    spl1_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f33,f74])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    v1_relat_1(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.54    inference(negated_conjecture,[],[f13])).
% 0.20/0.54  fof(f13,conjecture,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    spl1_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f34,f69])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    v1_funct_1(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    spl1_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f35,f64])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    v2_funct_1(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ~spl1_1 | ~spl1_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f36,f59,f55])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    spl1_2 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (25973)------------------------------
% 0.20/0.54  % (25973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25973)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (25973)Memory used [KB]: 10874
% 0.20/0.54  % (25973)Time elapsed: 0.071 s
% 0.20/0.54  % (25973)------------------------------
% 0.20/0.54  % (25973)------------------------------
% 0.20/0.54  % (25966)Success in time 0.181 s
%------------------------------------------------------------------------------
