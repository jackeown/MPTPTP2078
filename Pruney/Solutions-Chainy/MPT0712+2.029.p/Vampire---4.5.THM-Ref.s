%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 142 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  160 ( 325 expanded)
%              Number of equality atoms :   51 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f117,f169,f174,f185])).

fof(f185,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f47,f176,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f176,plain,
    ( k1_xboole_0 != k4_xboole_0(k9_relat_1(sK1,k2_tarski(sK0,sK0)),k9_relat_1(sK1,k2_tarski(sK0,sK0)))
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f84,f164])).

fof(f164,plain,
    ( k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_tarski(sK0,sK0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f162])).

% (4785)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f162,plain,
    ( spl2_3
  <=> k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f84,plain,(
    k1_xboole_0 != k4_xboole_0(k9_relat_1(sK1,k2_tarski(sK0,sK0)),k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f63,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f63,plain,(
    ~ r1_tarski(k9_relat_1(sK1,k2_tarski(sK0,sK0)),k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f49,f58])).

fof(f58,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f27,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

% (4791)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (4782)Refutation not found, incomplete strategy% (4782)------------------------------
% (4782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4782)Termination reason: Refutation not found, incomplete strategy

% (4782)Memory used [KB]: 10746
% (4782)Time elapsed: 0.122 s
% (4782)------------------------------
% (4782)------------------------------
% (4791)Refutation not found, incomplete strategy% (4791)------------------------------
% (4791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4791)Termination reason: Refutation not found, incomplete strategy

% (4791)Memory used [KB]: 10618
% (4791)Time elapsed: 0.123 s
% (4791)------------------------------
% (4791)------------------------------
% (4811)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (4799)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (4788)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (4805)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (4788)Refutation not found, incomplete strategy% (4788)------------------------------
% (4788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4788)Termination reason: Refutation not found, incomplete strategy

% (4788)Memory used [KB]: 10618
% (4788)Time elapsed: 0.134 s
% (4788)------------------------------
% (4788)------------------------------
% (4809)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (4801)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (4808)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (4802)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (4800)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (4810)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (4792)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (4789)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (4793)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (4807)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

fof(f49,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_tarski(sK0,sK0))),k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f29,f43,f43])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f174,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f55,f168])).

fof(f168,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl2_4
  <=> r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f55,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f169,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f160,f107,f166,f162])).

fof(f107,plain,
    ( spl2_1
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k9_relat_1(sK1,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X1))
        | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f160,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_tarski(sK0,sK0))
    | ~ spl2_1 ),
    inference(superposition,[],[f63,f157])).

fof(f157,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k9_relat_1(sK1,k2_tarski(X1,X1))
        | k9_relat_1(sK1,k2_tarski(X1,X1)) = k2_tarski(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1)) )
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f156,f40])).

fof(f40,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f156,plain,
    ( ! [X1] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k2_tarski(X1,X1))
        | k9_relat_1(sK1,k2_tarski(X1,X1)) = k2_tarski(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1)) )
    | ~ spl2_1 ),
    inference(superposition,[],[f58,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X0,X0))
        | k9_relat_1(sK1,k2_tarski(X0,X0)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) )
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | k9_relat_1(sK1,k2_tarski(X0,X0)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))
        | k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X0,X0)) )
    | ~ spl2_1 ),
    inference(equality_factoring,[],[f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X0,X0))
        | k9_relat_1(sK1,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X1))
        | k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X1,X1)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f131,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X0,X0)) ) ),
    inference(resolution,[],[f60,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f60,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(sK1))
      | k1_xboole_0 = k7_relat_1(sK1,X1) ) ),
    inference(resolution,[],[f27,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | k9_relat_1(sK1,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X1))
        | k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X0,X0)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f108,f83])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k9_relat_1(sK1,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X1))
        | ~ r2_hidden(X1,k1_relat_1(sK1)) )
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f117,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f27,f112])).

fof(f112,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f113,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f64,f110,f107])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | k9_relat_1(sK1,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) ) ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:01:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (4786)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (4795)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (4804)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (4796)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (4803)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (4803)Refutation not found, incomplete strategy% (4803)------------------------------
% 0.21/0.54  % (4803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4784)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (4798)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (4803)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  % (4797)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  
% 0.21/0.54  % (4803)Memory used [KB]: 10746
% 0.21/0.54  % (4803)Time elapsed: 0.111 s
% 0.21/0.54  % (4803)------------------------------
% 0.21/0.54  % (4803)------------------------------
% 0.21/0.54  % (4782)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (4790)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (4798)Refutation not found, incomplete strategy% (4798)------------------------------
% 0.21/0.54  % (4798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4798)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4798)Memory used [KB]: 10618
% 0.21/0.54  % (4798)Time elapsed: 0.125 s
% 0.21/0.54  % (4798)------------------------------
% 0.21/0.54  % (4798)------------------------------
% 0.21/0.54  % (4780)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (4787)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (4783)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (4790)Refutation not found, incomplete strategy% (4790)------------------------------
% 0.21/0.54  % (4790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4790)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4790)Memory used [KB]: 10618
% 0.21/0.54  % (4790)Time elapsed: 0.122 s
% 0.21/0.54  % (4790)------------------------------
% 0.21/0.54  % (4790)------------------------------
% 0.21/0.54  % (4781)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (4784)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f113,f117,f169,f174,f185])).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    ~spl2_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f182])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    $false | ~spl2_3),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f47,f176,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    k1_xboole_0 != k4_xboole_0(k9_relat_1(sK1,k2_tarski(sK0,sK0)),k9_relat_1(sK1,k2_tarski(sK0,sK0))) | ~spl2_3),
% 0.21/0.54    inference(backward_demodulation,[],[f84,f164])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_tarski(sK0,sK0)) | ~spl2_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f162])).
% 0.21/0.54  % (4785)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    spl2_3 <=> k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_tarski(sK0,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    k1_xboole_0 != k4_xboole_0(k9_relat_1(sK1,k2_tarski(sK0,sK0)),k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f63,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ~r1_tarski(k9_relat_1(sK1,k2_tarski(sK0,sK0)),k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.21/0.54    inference(backward_demodulation,[],[f49,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f27,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  % (4791)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (4782)Refutation not found, incomplete strategy% (4782)------------------------------
% 0.21/0.54  % (4782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4782)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4782)Memory used [KB]: 10746
% 0.21/0.54  % (4782)Time elapsed: 0.122 s
% 0.21/0.54  % (4782)------------------------------
% 0.21/0.54  % (4782)------------------------------
% 0.21/0.55  % (4791)Refutation not found, incomplete strategy% (4791)------------------------------
% 0.21/0.55  % (4791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4791)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4791)Memory used [KB]: 10618
% 0.21/0.55  % (4791)Time elapsed: 0.123 s
% 0.21/0.55  % (4791)------------------------------
% 0.21/0.55  % (4791)------------------------------
% 0.21/0.55  % (4811)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (4799)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (4788)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (4805)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (4788)Refutation not found, incomplete strategy% (4788)------------------------------
% 0.21/0.55  % (4788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4788)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4788)Memory used [KB]: 10618
% 0.21/0.55  % (4788)Time elapsed: 0.134 s
% 0.21/0.55  % (4788)------------------------------
% 0.21/0.55  % (4788)------------------------------
% 0.21/0.55  % (4809)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (4801)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (4808)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (4802)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (4800)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (4810)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (4792)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (4789)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (4793)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (4807)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    v1_relat_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.57    inference(negated_conjecture,[],[f15])).
% 0.21/0.57  fof(f15,conjecture,(
% 0.21/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_tarski(sK0,sK0))),k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.21/0.57    inference(definition_unfolding,[],[f29,f43,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).
% 0.21/0.57  fof(f174,plain,(
% 0.21/0.57    spl2_4),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    $false | spl2_4),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f55,f168])).
% 0.21/0.57  fof(f168,plain,(
% 0.21/0.57    ~r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | spl2_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f166])).
% 0.21/0.57  fof(f166,plain,(
% 0.21/0.57    spl2_4 <=> r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X1))) )),
% 0.21/0.57    inference(equality_resolution,[],[f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k2_tarski(X1,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f33,f43])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.57  fof(f169,plain,(
% 0.21/0.57    spl2_3 | ~spl2_4 | ~spl2_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f160,f107,f166,f162])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    spl2_1 <=> ! [X1,X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k9_relat_1(sK1,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) | ~r2_hidden(X1,k1_relat_1(sK1)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.57  fof(f160,plain,(
% 0.21/0.57    ~r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_tarski(sK0,sK0)) | ~spl2_1),
% 0.21/0.57    inference(superposition,[],[f63,f157])).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    ( ! [X1] : (k1_xboole_0 = k9_relat_1(sK1,k2_tarski(X1,X1)) | k9_relat_1(sK1,k2_tarski(X1,X1)) = k2_tarski(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1))) ) | ~spl2_1),
% 0.21/0.57    inference(forward_demodulation,[],[f156,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    ( ! [X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k2_tarski(X1,X1)) | k9_relat_1(sK1,k2_tarski(X1,X1)) = k2_tarski(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1))) ) | ~spl2_1),
% 0.21/0.57    inference(superposition,[],[f58,f154])).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X0,X0)) | k9_relat_1(sK1,k2_tarski(X0,X0)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))) ) | ~spl2_1),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f153])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k9_relat_1(sK1,k2_tarski(X0,X0)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) | k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X0,X0))) ) | ~spl2_1),
% 0.21/0.57    inference(equality_factoring,[],[f145])).
% 0.21/0.57  fof(f145,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X0,X0)) | k9_relat_1(sK1,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) | k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X1,X1))) ) | ~spl2_1),
% 0.21/0.57    inference(resolution,[],[f131,f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X0,X0))) )),
% 0.21/0.57    inference(resolution,[],[f60,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f42,f43])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X1] : (~r1_xboole_0(X1,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,X1)) )),
% 0.21/0.57    inference(resolution,[],[f27,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k9_relat_1(sK1,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) | k1_xboole_0 = k7_relat_1(sK1,k2_tarski(X0,X0))) ) | ~spl2_1),
% 0.21/0.57    inference(resolution,[],[f108,f83])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK1)) | k9_relat_1(sK1,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X1)) | ~r2_hidden(X1,k1_relat_1(sK1))) ) | ~spl2_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f107])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    spl2_2),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    $false | spl2_2),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f27,f112])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    ~v1_relat_1(sK1) | spl2_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f110])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    spl2_1 | ~spl2_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f64,f110,f107])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | k9_relat_1(sK1,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X1))) )),
% 0.21/0.57    inference(resolution,[],[f28,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X1,k1_relat_1(X2)) | k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(flattening,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    v1_funct_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (4784)------------------------------
% 0.21/0.57  % (4784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (4784)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (4784)Memory used [KB]: 6396
% 0.21/0.57  % (4784)Time elapsed: 0.130 s
% 0.21/0.57  % (4784)------------------------------
% 0.21/0.57  % (4784)------------------------------
% 0.21/0.57  % (4775)Success in time 0.206 s
%------------------------------------------------------------------------------
