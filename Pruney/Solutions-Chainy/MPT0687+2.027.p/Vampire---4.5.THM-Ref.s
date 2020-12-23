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
% DateTime   : Thu Dec  3 12:53:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 139 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  191 ( 317 expanded)
%              Number of equality atoms :   54 ( 118 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f57,f72,f74,f83,f96,f100,f109])).

fof(f109,plain,(
    ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f106])).

fof(f106,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_5 ),
    inference(superposition,[],[f58,f91])).

fof(f91,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl2_5
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[],[f44,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f30,f41])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f100,plain,
    ( ~ spl2_1
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | ~ spl2_1
    | spl2_6 ),
    inference(resolution,[],[f98,f50])).

fof(f50,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f98,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl2_6 ),
    inference(resolution,[],[f95,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f95,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_6
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f96,plain,
    ( ~ spl2_3
    | spl2_5
    | ~ spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f87,f53,f93,f89,f65])).

fof(f65,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f53,plain,
    ( spl2_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f87,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f84])).

fof(f84,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f34,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f83,plain,
    ( spl2_1
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl2_1
    | spl2_4 ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f79,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | spl2_4 ),
    inference(resolution,[],[f78,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f78,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | spl2_4 ),
    inference(resolution,[],[f71,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f71,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_4
  <=> r1_xboole_0(k2_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f74,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f67,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

% (17904)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f22,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f67,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f72,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f63,f53,f69,f65])).

fof(f63,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f60])).

fof(f60,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(superposition,[],[f54,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f54,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f57,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f43,f53,f49])).

fof(f43,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f26,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f42,f53,f49])).

fof(f42,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f27,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:50:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.44  % (17905)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (17911)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.45  % (17909)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.45  % (17908)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.45  % (17913)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.45  % (17906)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (17901)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.45  % (17905)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f56,f57,f72,f74,f83,f96,f100,f109])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    ~spl2_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f108])).
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    $false | ~spl2_5),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f106])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    k1_xboole_0 != k1_xboole_0 | ~spl2_5),
% 0.20/0.46    inference(superposition,[],[f58,f91])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f89])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    spl2_5 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 != k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.46    inference(superposition,[],[f44,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f30,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f29,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f31,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    ~spl2_1 | spl2_6),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f99])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    $false | (~spl2_1 | spl2_6)),
% 0.20/0.46    inference(resolution,[],[f98,f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    spl2_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl2_6),
% 0.20/0.46    inference(resolution,[],[f95,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f38,f41])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK1)) | spl2_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f93])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    spl2_6 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ~spl2_3 | spl2_5 | ~spl2_6 | ~spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f87,f53,f93,f89,f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl2_3 <=> v1_relat_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    spl2_2 <=> k1_xboole_0 = k10_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK1)) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f84])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK1)) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.46    inference(superposition,[],[f34,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    k1_xboole_0 = k10_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f53])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    spl2_1 | spl2_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f82])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    $false | (spl2_1 | spl2_4)),
% 0.20/0.46    inference(resolution,[],[f79,f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f49])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    r2_hidden(sK0,k2_relat_1(sK1)) | spl2_4),
% 0.20/0.46    inference(resolution,[],[f78,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f35,f41])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_relat_1(sK1)) | spl2_4),
% 0.20/0.46    inference(resolution,[],[f71,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ~r1_xboole_0(k2_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f69])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    spl2_4 <=> r1_xboole_0(k2_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    spl2_3),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f73])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    $false | spl2_3),
% 0.20/0.46    inference(resolution,[],[f67,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  % (17904)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.20/0.46    inference(nnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.20/0.46    inference(negated_conjecture,[],[f11])).
% 0.20/0.46  fof(f11,conjecture,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ~v1_relat_1(sK1) | spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f65])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    ~spl2_3 | ~spl2_4 | spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f63,f53,f69,f65])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ~r1_xboole_0(k2_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | spl2_2),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | spl2_2),
% 0.20/0.46    inference(superposition,[],[f54,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(nnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    k1_xboole_0 != k10_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f53])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl2_1 | ~spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f43,f53,f49])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    k1_xboole_0 != k10_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.46    inference(definition_unfolding,[],[f26,f41])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ~spl2_1 | spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f42,f53,f49])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    k1_xboole_0 = k10_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.46    inference(definition_unfolding,[],[f27,f41])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (17905)------------------------------
% 0.20/0.46  % (17905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (17905)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (17905)Memory used [KB]: 6140
% 0.20/0.46  % (17905)Time elapsed: 0.052 s
% 0.20/0.46  % (17905)------------------------------
% 0.20/0.46  % (17905)------------------------------
% 0.20/0.46  % (17900)Success in time 0.115 s
%------------------------------------------------------------------------------
