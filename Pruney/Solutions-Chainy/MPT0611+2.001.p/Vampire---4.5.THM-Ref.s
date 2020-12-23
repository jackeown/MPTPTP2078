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
% DateTime   : Thu Dec  3 12:51:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 123 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :    6
%              Number of atoms          :  212 ( 332 expanded)
%              Number of equality atoms :   28 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f588,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f122,f126,f130,f154,f158,f198,f202,f220,f250,f353,f454,f521,f534,f555,f587])).

fof(f587,plain,
    ( spl12_3
    | ~ spl12_21
    | ~ spl12_73 ),
    inference(avatar_contradiction_clause,[],[f586])).

fof(f586,plain,
    ( $false
    | spl12_3
    | ~ spl12_21
    | ~ spl12_73 ),
    inference(subsumption_resolution,[],[f584,f125])).

fof(f125,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl12_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl12_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f584,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl12_21
    | ~ spl12_73 ),
    inference(trivial_inequality_removal,[],[f582])).

fof(f582,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1)
    | ~ spl12_21
    | ~ spl12_73 ),
    inference(superposition,[],[f197,f554])).

fof(f554,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl12_73 ),
    inference(avatar_component_clause,[],[f553])).

fof(f553,plain,
    ( spl12_73
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_73])])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl12_21 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl12_21
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).

fof(f555,plain,
    ( ~ spl12_69
    | spl12_73
    | ~ spl12_11
    | ~ spl12_68 ),
    inference(avatar_split_clause,[],[f539,f516,f156,f553,f519])).

fof(f519,plain,
    ( spl12_69
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_69])])).

fof(f156,plain,
    ( spl12_11
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f516,plain,
    ( spl12_68
  <=> k3_xboole_0(sK0,sK1) = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_68])])).

fof(f539,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl12_11
    | ~ spl12_68 ),
    inference(superposition,[],[f517,f157])).

fof(f157,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f517,plain,
    ( k3_xboole_0(sK0,sK1) = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | ~ spl12_68 ),
    inference(avatar_component_clause,[],[f516])).

fof(f534,plain,
    ( ~ spl12_2
    | ~ spl12_10
    | spl12_69 ),
    inference(avatar_contradiction_clause,[],[f533])).

fof(f533,plain,
    ( $false
    | ~ spl12_2
    | ~ spl12_10
    | spl12_69 ),
    inference(subsumption_resolution,[],[f529,f121])).

fof(f121,plain,
    ( v1_relat_1(sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl12_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f529,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl12_10
    | spl12_69 ),
    inference(resolution,[],[f520,f153])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl12_10
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f520,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl12_69 ),
    inference(avatar_component_clause,[],[f519])).

fof(f521,plain,
    ( spl12_68
    | ~ spl12_69
    | ~ spl12_31
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f463,f452,f248,f519,f516])).

fof(f248,plain,
    ( spl12_31
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f452,plain,
    ( spl12_62
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).

fof(f463,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | k3_xboole_0(sK0,sK1) = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | ~ spl12_31
    | ~ spl12_62 ),
    inference(resolution,[],[f453,f249])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = X1 )
    | ~ spl12_31 ),
    inference(avatar_component_clause,[],[f248])).

fof(f453,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl12_62 ),
    inference(avatar_component_clause,[],[f452])).

fof(f454,plain,
    ( spl12_62
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_25
    | ~ spl12_51 ),
    inference(avatar_split_clause,[],[f420,f351,f218,f120,f116,f452])).

fof(f116,plain,
    ( spl12_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f218,plain,
    ( spl12_25
  <=> k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f351,plain,
    ( spl12_51
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_51])])).

fof(f420,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_25
    | ~ spl12_51 ),
    inference(subsumption_resolution,[],[f419,f121])).

fof(f419,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ spl12_1
    | ~ spl12_25
    | ~ spl12_51 ),
    inference(subsumption_resolution,[],[f416,f117])).

fof(f117,plain,
    ( v1_relat_1(sK1)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f416,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl12_25
    | ~ spl12_51 ),
    inference(superposition,[],[f352,f219])).

fof(f219,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl12_25 ),
    inference(avatar_component_clause,[],[f218])).

fof(f352,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl12_51 ),
    inference(avatar_component_clause,[],[f351])).

fof(f353,plain,(
    spl12_51 ),
    inference(avatar_split_clause,[],[f79,f351])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f250,plain,(
    spl12_31 ),
    inference(avatar_split_clause,[],[f98,f248])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f220,plain,
    ( spl12_25
    | ~ spl12_4
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f215,f200,f128,f218])).

fof(f128,plain,
    ( spl12_4
  <=> r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f200,plain,
    ( spl12_22
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f215,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl12_4
    | ~ spl12_22 ),
    inference(resolution,[],[f201,f129])).

fof(f129,plain,
    ( r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,(
    spl12_22 ),
    inference(avatar_split_clause,[],[f104,f200])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f198,plain,(
    spl12_21 ),
    inference(avatar_split_clause,[],[f103,f196])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f158,plain,(
    spl12_11 ),
    inference(avatar_split_clause,[],[f71,f156])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f154,plain,(
    spl12_10 ),
    inference(avatar_split_clause,[],[f93,f152])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f130,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f64,f128])).

fof(f64,plain,(
    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

fof(f126,plain,(
    ~ spl12_3 ),
    inference(avatar_split_clause,[],[f65,f124])).

fof(f65,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f122,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f66,f120])).

fof(f66,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f118,plain,(
    spl12_1 ),
    inference(avatar_split_clause,[],[f63,f116])).

fof(f63,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:09:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (19012)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (19030)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (19030)Refutation not found, incomplete strategy% (19030)------------------------------
% 0.22/0.48  % (19030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (19030)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (19030)Memory used [KB]: 10618
% 0.22/0.48  % (19030)Time elapsed: 0.006 s
% 0.22/0.48  % (19030)------------------------------
% 0.22/0.48  % (19030)------------------------------
% 0.22/0.49  % (19023)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (19018)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (19014)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (19017)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (19019)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (19024)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (19015)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (19009)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (19029)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (19013)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (19011)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (19022)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (19011)Refutation not found, incomplete strategy% (19011)------------------------------
% 0.22/0.52  % (19011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19011)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19011)Memory used [KB]: 10618
% 0.22/0.52  % (19011)Time elapsed: 0.099 s
% 0.22/0.52  % (19011)------------------------------
% 0.22/0.52  % (19011)------------------------------
% 0.22/0.52  % (19026)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (19020)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (19020)Refutation not found, incomplete strategy% (19020)------------------------------
% 0.22/0.52  % (19020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19020)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19020)Memory used [KB]: 6012
% 0.22/0.52  % (19020)Time elapsed: 0.103 s
% 0.22/0.52  % (19020)------------------------------
% 0.22/0.52  % (19020)------------------------------
% 0.22/0.52  % (19028)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (19016)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.53  % (19019)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f588,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f118,f122,f126,f130,f154,f158,f198,f202,f220,f250,f353,f454,f521,f534,f555,f587])).
% 0.22/0.53  fof(f587,plain,(
% 0.22/0.53    spl12_3 | ~spl12_21 | ~spl12_73),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f586])).
% 0.22/0.53  fof(f586,plain,(
% 0.22/0.53    $false | (spl12_3 | ~spl12_21 | ~spl12_73)),
% 0.22/0.53    inference(subsumption_resolution,[],[f584,f125])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ~r1_xboole_0(sK0,sK1) | spl12_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f124])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    spl12_3 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.22/0.53  fof(f584,plain,(
% 0.22/0.53    r1_xboole_0(sK0,sK1) | (~spl12_21 | ~spl12_73)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f582])).
% 0.22/0.53  fof(f582,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1) | (~spl12_21 | ~spl12_73)),
% 0.22/0.53    inference(superposition,[],[f197,f554])).
% 0.22/0.53  fof(f554,plain,(
% 0.22/0.53    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl12_73),
% 0.22/0.53    inference(avatar_component_clause,[],[f553])).
% 0.22/0.53  fof(f553,plain,(
% 0.22/0.53    spl12_73 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_73])])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl12_21),
% 0.22/0.53    inference(avatar_component_clause,[],[f196])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    spl12_21 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).
% 0.22/0.53  fof(f555,plain,(
% 0.22/0.53    ~spl12_69 | spl12_73 | ~spl12_11 | ~spl12_68),
% 0.22/0.53    inference(avatar_split_clause,[],[f539,f516,f156,f553,f519])).
% 0.22/0.53  fof(f519,plain,(
% 0.22/0.53    spl12_69 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_69])])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    spl12_11 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 0.22/0.53  fof(f516,plain,(
% 0.22/0.53    spl12_68 <=> k3_xboole_0(sK0,sK1) = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_68])])).
% 0.22/0.53  fof(f539,plain,(
% 0.22/0.53    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl12_11 | ~spl12_68)),
% 0.22/0.53    inference(superposition,[],[f517,f157])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) ) | ~spl12_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f156])).
% 0.22/0.53  fof(f517,plain,(
% 0.22/0.53    k3_xboole_0(sK0,sK1) = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,sK1)) | ~spl12_68),
% 0.22/0.53    inference(avatar_component_clause,[],[f516])).
% 0.22/0.53  fof(f534,plain,(
% 0.22/0.53    ~spl12_2 | ~spl12_10 | spl12_69),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f533])).
% 0.22/0.53  fof(f533,plain,(
% 0.22/0.53    $false | (~spl12_2 | ~spl12_10 | spl12_69)),
% 0.22/0.53    inference(subsumption_resolution,[],[f529,f121])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    v1_relat_1(sK0) | ~spl12_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl12_2 <=> v1_relat_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.22/0.53  fof(f529,plain,(
% 0.22/0.53    ~v1_relat_1(sK0) | (~spl12_10 | spl12_69)),
% 0.22/0.53    inference(resolution,[],[f520,f153])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl12_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f152])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    spl12_10 <=> ! [X1,X0] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 0.22/0.53  fof(f520,plain,(
% 0.22/0.53    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl12_69),
% 0.22/0.53    inference(avatar_component_clause,[],[f519])).
% 0.22/0.53  fof(f521,plain,(
% 0.22/0.53    spl12_68 | ~spl12_69 | ~spl12_31 | ~spl12_62),
% 0.22/0.53    inference(avatar_split_clause,[],[f463,f452,f248,f519,f516])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    spl12_31 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).
% 0.22/0.53  fof(f452,plain,(
% 0.22/0.53    spl12_62 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).
% 0.22/0.53  fof(f463,plain,(
% 0.22/0.53    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | k3_xboole_0(sK0,sK1) = k8_relat_1(k1_xboole_0,k3_xboole_0(sK0,sK1)) | (~spl12_31 | ~spl12_62)),
% 0.22/0.53    inference(resolution,[],[f453,f249])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) ) | ~spl12_31),
% 0.22/0.53    inference(avatar_component_clause,[],[f248])).
% 0.22/0.53  fof(f453,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl12_62),
% 0.22/0.53    inference(avatar_component_clause,[],[f452])).
% 0.22/0.53  fof(f454,plain,(
% 0.22/0.53    spl12_62 | ~spl12_1 | ~spl12_2 | ~spl12_25 | ~spl12_51),
% 0.22/0.53    inference(avatar_split_clause,[],[f420,f351,f218,f120,f116,f452])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    spl12_1 <=> v1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    spl12_25 <=> k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).
% 0.22/0.53  fof(f351,plain,(
% 0.22/0.53    spl12_51 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_51])])).
% 0.22/0.53  fof(f420,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | (~spl12_1 | ~spl12_2 | ~spl12_25 | ~spl12_51)),
% 0.22/0.53    inference(subsumption_resolution,[],[f419,f121])).
% 0.22/0.53  fof(f419,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~v1_relat_1(sK0) | (~spl12_1 | ~spl12_25 | ~spl12_51)),
% 0.22/0.53    inference(subsumption_resolution,[],[f416,f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    v1_relat_1(sK1) | ~spl12_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f116])).
% 0.22/0.53  fof(f416,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | (~spl12_25 | ~spl12_51)),
% 0.22/0.53    inference(superposition,[],[f352,f219])).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl12_25),
% 0.22/0.53    inference(avatar_component_clause,[],[f218])).
% 0.22/0.53  fof(f352,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl12_51),
% 0.22/0.53    inference(avatar_component_clause,[],[f351])).
% 0.22/0.53  fof(f353,plain,(
% 0.22/0.53    spl12_51),
% 0.22/0.53    inference(avatar_split_clause,[],[f79,f351])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    spl12_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f98,f248])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    spl12_25 | ~spl12_4 | ~spl12_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f215,f200,f128,f218])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    spl12_4 <=> r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    spl12_22 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).
% 0.22/0.53  fof(f215,plain,(
% 0.22/0.53    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) | (~spl12_4 | ~spl12_22)),
% 0.22/0.53    inference(resolution,[],[f201,f129])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl12_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f128])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl12_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f200])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    spl12_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f104,f200])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    spl12_21),
% 0.22/0.53    inference(avatar_split_clause,[],[f103,f196])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    spl12_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f71,f156])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    spl12_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f93,f152])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    spl12_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f64,f128])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f29])).
% 0.22/0.53  fof(f29,conjecture,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ~spl12_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f65,f124])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ~r1_xboole_0(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    spl12_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f66,f120])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl12_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f63,f116])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (19019)------------------------------
% 0.22/0.53  % (19019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19019)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (19019)Memory used [KB]: 11001
% 0.22/0.53  % (19019)Time elapsed: 0.099 s
% 0.22/0.53  % (19019)------------------------------
% 0.22/0.53  % (19019)------------------------------
% 0.22/0.53  % (19008)Success in time 0.166 s
%------------------------------------------------------------------------------
