%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 136 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  232 ( 396 expanded)
%              Number of equality atoms :   39 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f43,f62,f77,f83,f106,f118,f124,f126])).

fof(f126,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl5_9 ),
    inference(resolution,[],[f105,f23])).

fof(f23,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f105,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(sK4(sK0,sK1)),k1_tarski(X0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_9
  <=> ! [X0] : ~ r1_tarski(k1_tarski(sK4(sK0,sK1)),k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f124,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl5_6 ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,
    ( ! [X1] : k1_tarski(X1) != k1_tarski(sK2(sK3(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_6
  <=> ! [X1] : k1_tarski(X1) != k1_tarski(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f118,plain,
    ( ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f114,f24])).

fof(f24,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f114,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,k1_tarski(X0))
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f42,f102])).

fof(f102,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_8
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f42,plain,
    ( ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_4
  <=> ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f106,plain,
    ( spl5_8
    | spl5_9
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f93,f41,f37,f31,f26,f104,f100])).

fof(f26,plain,
    ( spl5_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f31,plain,
    ( spl5_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f37,plain,
    ( spl5_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(sK4(sK0,sK1)),k1_tarski(X0))
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(superposition,[],[f42,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0))
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f88,f35])).

fof(f35,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK0))
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f28,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
      | r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f28,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK0))
        | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f87,f28])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK0))
        | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0)) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f86,f33])).

fof(f33,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK0))
        | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f38,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] :
            ~ ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
              & r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).

fof(f38,plain,
    ( v2_funct_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f83,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | spl5_7 ),
    inference(subsumption_resolution,[],[f81,f28])).

fof(f81,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl5_2
    | spl5_3
    | spl5_7 ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f39,plain,
    ( ~ v2_funct_1(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f80,plain,
    ( v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | spl5_7 ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f78,plain,
    ( ~ v1_funct_1(sK0)
    | v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl5_7 ),
    inference(resolution,[],[f76,f15])).

fof(f15,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f76,plain,
    ( ~ r2_hidden(sK3(sK0),k2_relat_1(sK0))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_7
  <=> r2_hidden(sK3(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f77,plain,
    ( ~ spl5_7
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f72,f56,f26,f74])).

fof(f56,plain,
    ( spl5_5
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f72,plain,
    ( ~ r2_hidden(sK3(sK0),k2_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f68,f28])).

fof(f68,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK3(sK0),k2_relat_1(sK0))
    | ~ spl5_5 ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK3(sK0),k2_relat_1(sK0))
    | ~ spl5_5 ),
    inference(superposition,[],[f19,f58])).

fof(f58,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,
    ( spl5_5
    | spl5_6
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f52,f37,f31,f26,f60,f56])).

fof(f52,plain,
    ( ! [X1] :
        ( k1_tarski(X1) != k1_tarski(sK2(sK3(sK0)))
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0))) )
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f51,f28])).

fof(f51,plain,
    ( ! [X1] :
        ( k1_tarski(X1) != k1_tarski(sK2(sK3(sK0)))
        | ~ v1_relat_1(sK0)
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0))) )
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f50,f39])).

fof(f50,plain,
    ( ! [X1] :
        ( k1_tarski(X1) != k1_tarski(sK2(sK3(sK0)))
        | v2_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0))) )
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f47,f33])).

fof(f47,plain,
    ( ! [X1] :
        ( k1_tarski(X1) != k1_tarski(sK2(sK3(sK0)))
        | ~ v1_funct_1(sK0)
        | v2_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0))) )
    | spl5_3 ),
    inference(superposition,[],[f16,f45])).

fof(f45,plain,
    ( ! [X0] :
        ( k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK2(X0))
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) )
    | spl5_3 ),
    inference(resolution,[],[f44,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f44,plain,
    ( ! [X1] : r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(sK2(X1)))
    | spl5_3 ),
    inference(subsumption_resolution,[],[f11,f39])).

fof(f11,plain,(
    ! [X1] :
      ( r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(sK2(X1)))
      | v2_funct_1(sK0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
        <=> ! [X1] :
            ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_1)).

fof(f16,plain,(
    ! [X2,X0] :
      ( k1_tarski(X2) != k10_relat_1(X0,k1_tarski(sK3(X0)))
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f12,f41,f37])).

fof(f12,plain,(
    ! [X2] :
      ( ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
      | ~ v2_funct_1(sK0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f13,f26])).

fof(f13,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:04:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (4289)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (4294)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  % (4289)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (4301)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f29,f34,f43,f62,f77,f83,f106,f118,f124,f126])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ~spl5_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f125])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    $false | ~spl5_9),
% 0.22/0.48    inference(resolution,[],[f105,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(k1_tarski(sK4(sK0,sK1)),k1_tarski(X0))) ) | ~spl5_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f104])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    spl5_9 <=> ! [X0] : ~r1_tarski(k1_tarski(sK4(sK0,sK1)),k1_tarski(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    ~spl5_6),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f123])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    $false | ~spl5_6),
% 0.22/0.48    inference(equality_resolution,[],[f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK2(sK3(sK0)))) ) | ~spl5_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl5_6 <=> ! [X1] : k1_tarski(X1) != k1_tarski(sK2(sK3(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ~spl5_4 | ~spl5_8),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f117])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    $false | (~spl5_4 | ~spl5_8)),
% 0.22/0.48    inference(subsumption_resolution,[],[f114,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_tarski(X0))) ) | (~spl5_4 | ~spl5_8)),
% 0.22/0.48    inference(superposition,[],[f42,f102])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1)) | ~spl5_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f100])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    spl5_8 <=> k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X2] : (~r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))) ) | ~spl5_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    spl5_4 <=> ! [X2] : ~r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    spl5_8 | spl5_9 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f93,f41,f37,f31,f26,f104,f100])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    spl5_1 <=> v1_relat_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    spl5_2 <=> v1_funct_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    spl5_3 <=> v2_funct_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(k1_tarski(sK4(sK0,sK1)),k1_tarski(X0)) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1))) ) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.22/0.48    inference(superposition,[],[f42,f90])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X0] : (k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0)) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0))) ) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.22/0.48    inference(resolution,[],[f88,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK0)) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0))) ) | ~spl5_1),
% 0.22/0.48    inference(resolution,[],[f28,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    v1_relat_1(sK0) | ~spl5_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f26])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0))) ) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f87,f28])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(sK0) | ~r2_hidden(X0,k2_relat_1(sK0)) | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0))) ) | (~spl5_2 | ~spl5_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f86,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v1_funct_1(sK0) | ~spl5_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f31])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~r2_hidden(X0,k2_relat_1(sK0)) | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK4(sK0,X0))) ) | ~spl5_3),
% 0.22/0.48    inference(resolution,[],[f38,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k2_relat_1(X0)) | k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK4(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (! [X1] : ~(! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    v2_funct_1(sK0) | ~spl5_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f37])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ~spl5_1 | ~spl5_2 | spl5_3 | spl5_7),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f82])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    $false | (~spl5_1 | ~spl5_2 | spl5_3 | spl5_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f81,f28])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ~v1_relat_1(sK0) | (~spl5_2 | spl5_3 | spl5_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f80,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ~v2_funct_1(sK0) | spl5_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f37])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    v2_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl5_2 | spl5_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f78,f33])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ~v1_funct_1(sK0) | v2_funct_1(sK0) | ~v1_relat_1(sK0) | spl5_7),
% 0.22/0.48    inference(resolution,[],[f76,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK3(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ~r2_hidden(sK3(sK0),k2_relat_1(sK0)) | spl5_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl5_7 <=> r2_hidden(sK3(sK0),k2_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ~spl5_7 | ~spl5_1 | ~spl5_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f72,f56,f26,f74])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl5_5 <=> k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ~r2_hidden(sK3(sK0),k2_relat_1(sK0)) | (~spl5_1 | ~spl5_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f68,f28])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ~v1_relat_1(sK0) | ~r2_hidden(sK3(sK0),k2_relat_1(sK0)) | ~spl5_5),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | ~r2_hidden(sK3(sK0),k2_relat_1(sK0)) | ~spl5_5),
% 0.22/0.48    inference(superposition,[],[f19,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0))) | ~spl5_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f56])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | ~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl5_5 | spl5_6 | ~spl5_1 | ~spl5_2 | spl5_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f52,f37,f31,f26,f60,f56])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK2(sK3(sK0))) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0)))) ) | (~spl5_1 | ~spl5_2 | spl5_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f51,f28])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK2(sK3(sK0))) | ~v1_relat_1(sK0) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0)))) ) | (~spl5_2 | spl5_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f50,f39])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK2(sK3(sK0))) | v2_funct_1(sK0) | ~v1_relat_1(sK0) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0)))) ) | (~spl5_2 | spl5_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f47,f33])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK2(sK3(sK0))) | ~v1_funct_1(sK0) | v2_funct_1(sK0) | ~v1_relat_1(sK0) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK3(sK0)))) ) | spl5_3),
% 0.22/0.48    inference(superposition,[],[f16,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0] : (k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK2(X0)) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0))) ) | spl5_3),
% 0.22/0.48    inference(resolution,[],[f44,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(sK2(X1)))) ) | spl5_3),
% 0.22/0.48    inference(subsumption_resolution,[],[f11,f39])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(sK2(X1))) | v2_funct_1(sK0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0] : ((v2_funct_1(X0) <~> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0] : ((v2_funct_1(X0) <~> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_1)).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X2,X0] : (k1_tarski(X2) != k10_relat_1(X0,k1_tarski(sK3(X0))) | ~v1_funct_1(X0) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ~spl5_3 | spl5_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f12,f41,f37])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ( ! [X2] : (~r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2)) | ~v2_funct_1(sK0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    spl5_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f14,f31])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    v1_funct_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    spl5_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f13,f26])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    v1_relat_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (4289)------------------------------
% 0.22/0.48  % (4289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (4289)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (4289)Memory used [KB]: 10618
% 0.22/0.48  % (4289)Time elapsed: 0.057 s
% 0.22/0.48  % (4289)------------------------------
% 0.22/0.48  % (4289)------------------------------
% 0.22/0.48  % (4285)Success in time 0.118 s
%------------------------------------------------------------------------------
