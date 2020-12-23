%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:40 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 112 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 323 expanded)
%              Number of equality atoms :   24 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f589,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f50,f166,f588])).

fof(f588,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f587])).

fof(f587,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f571,f291])).

fof(f291,plain,
    ( ! [X0] : r2_hidden(sK2(k2_tarski(sK0,X0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f282,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f282,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK0,X0),k2_relat_1(sK1))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f168,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f168,plain,
    ( ! [X0] : k2_tarski(sK0,X0) != k4_xboole_0(k2_tarski(sK0,X0),k2_relat_1(sK1))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f43,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f43,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f571,plain,
    ( ~ r2_hidden(sK2(k2_tarski(sK0,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f290,f213])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK0))
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f188,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f188,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f18,f48,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f48,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f290,plain,
    ( ! [X0] : r2_hidden(sK2(k2_tarski(sK0,X0),k2_relat_1(sK1)),k2_tarski(sK0,X0))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f282,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f166,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f156,f79])).

fof(f79,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f74,f26])).

fof(f74,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f18,f47,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k2_tarski(sK0,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f156,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK1),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f122,f78,f24])).

fof(f78,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),k2_tarski(sK0,sK0)),k2_relat_1(sK1))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f74,f25])).

fof(f122,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),k2_relat_1(sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f55,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_relat_1(sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f44,f44,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X1,X2)
      | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f50,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f37,f46,f42])).

fof(f37,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k2_tarski(sK0,sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f16,f21])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f36,f46,f42])).

fof(f36,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f17,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:50:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (13112)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (13128)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (13120)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (13117)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (13115)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (13111)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (13113)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (13124)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (13134)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (13126)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (13140)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (13114)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (13126)Refutation not found, incomplete strategy% (13126)------------------------------
% 0.22/0.53  % (13126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13133)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (13126)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13126)Memory used [KB]: 6140
% 0.22/0.53  % (13126)Time elapsed: 0.005 s
% 0.22/0.53  % (13126)------------------------------
% 0.22/0.53  % (13126)------------------------------
% 0.22/0.53  % (13138)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (13127)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (13125)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (13136)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (13132)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (13139)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (13116)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (13118)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (13133)Refutation not found, incomplete strategy% (13133)------------------------------
% 0.22/0.54  % (13133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (13133)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (13133)Memory used [KB]: 10618
% 1.37/0.54  % (13133)Time elapsed: 0.133 s
% 1.37/0.54  % (13133)------------------------------
% 1.37/0.54  % (13133)------------------------------
% 1.37/0.54  % (13131)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.55  % (13123)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.55  % (13120)Refutation found. Thanks to Tanya!
% 1.37/0.55  % SZS status Theorem for theBenchmark
% 1.37/0.55  % (13130)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.55  % (13119)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.55  % (13122)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.52/0.56  % (13122)Refutation not found, incomplete strategy% (13122)------------------------------
% 1.52/0.56  % (13122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (13122)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (13122)Memory used [KB]: 10618
% 1.52/0.56  % (13122)Time elapsed: 0.150 s
% 1.52/0.56  % (13122)------------------------------
% 1.52/0.56  % (13122)------------------------------
% 1.52/0.56  % SZS output start Proof for theBenchmark
% 1.52/0.56  fof(f589,plain,(
% 1.52/0.56    $false),
% 1.52/0.56    inference(avatar_sat_refutation,[],[f49,f50,f166,f588])).
% 1.52/0.56  fof(f588,plain,(
% 1.52/0.56    ~spl4_1 | ~spl4_2),
% 1.52/0.56    inference(avatar_contradiction_clause,[],[f587])).
% 1.52/0.56  fof(f587,plain,(
% 1.52/0.56    $false | (~spl4_1 | ~spl4_2)),
% 1.52/0.56    inference(subsumption_resolution,[],[f571,f291])).
% 1.52/0.56  fof(f291,plain,(
% 1.52/0.56    ( ! [X0] : (r2_hidden(sK2(k2_tarski(sK0,X0),k2_relat_1(sK1)),k2_relat_1(sK1))) ) | ~spl4_1),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f282,f26])).
% 1.52/0.56  fof(f26,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f15])).
% 1.52/0.56  fof(f15,plain,(
% 1.52/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.52/0.56    inference(ennf_transformation,[],[f12])).
% 1.52/0.56  fof(f12,plain,(
% 1.52/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.52/0.56    inference(rectify,[],[f2])).
% 1.52/0.56  fof(f2,axiom,(
% 1.52/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.52/0.56  fof(f282,plain,(
% 1.52/0.56    ( ! [X0] : (~r1_xboole_0(k2_tarski(sK0,X0),k2_relat_1(sK1))) ) | ~spl4_1),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f168,f23])).
% 1.52/0.56  fof(f23,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f3])).
% 1.52/0.56  fof(f3,axiom,(
% 1.52/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.52/0.56  fof(f168,plain,(
% 1.52/0.56    ( ! [X0] : (k2_tarski(sK0,X0) != k4_xboole_0(k2_tarski(sK0,X0),k2_relat_1(sK1))) ) | ~spl4_1),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f43,f27])).
% 1.52/0.56  fof(f27,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f8])).
% 1.52/0.56  fof(f8,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.52/0.56  fof(f43,plain,(
% 1.52/0.56    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl4_1),
% 1.52/0.56    inference(avatar_component_clause,[],[f42])).
% 1.52/0.56  fof(f42,plain,(
% 1.52/0.56    spl4_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.52/0.56  fof(f571,plain,(
% 1.52/0.56    ~r2_hidden(sK2(k2_tarski(sK0,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) | (~spl4_1 | ~spl4_2)),
% 1.52/0.56    inference(resolution,[],[f290,f213])).
% 1.52/0.56  fof(f213,plain,(
% 1.52/0.56    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK0,sK0)) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl4_2),
% 1.52/0.56    inference(resolution,[],[f188,f24])).
% 1.52/0.56  fof(f24,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f15])).
% 1.52/0.56  fof(f188,plain,(
% 1.52/0.56    r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0)) | ~spl4_2),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f18,f48,f20])).
% 1.52/0.56  fof(f20,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0) )),
% 1.52/0.56    inference(cnf_transformation,[],[f14])).
% 1.52/0.56  fof(f14,plain,(
% 1.52/0.56    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f9])).
% 1.52/0.56  fof(f9,axiom,(
% 1.52/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 1.52/0.56  fof(f48,plain,(
% 1.52/0.56    k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0)) | ~spl4_2),
% 1.52/0.56    inference(avatar_component_clause,[],[f46])).
% 1.52/0.56  fof(f46,plain,(
% 1.52/0.56    spl4_2 <=> k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0))),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.52/0.56  fof(f18,plain,(
% 1.52/0.56    v1_relat_1(sK1)),
% 1.52/0.56    inference(cnf_transformation,[],[f13])).
% 1.52/0.56  fof(f13,plain,(
% 1.52/0.56    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f11])).
% 1.52/0.56  fof(f11,negated_conjecture,(
% 1.52/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 1.52/0.56    inference(negated_conjecture,[],[f10])).
% 1.52/0.56  fof(f10,conjecture,(
% 1.52/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 1.52/0.56  fof(f290,plain,(
% 1.52/0.56    ( ! [X0] : (r2_hidden(sK2(k2_tarski(sK0,X0),k2_relat_1(sK1)),k2_tarski(sK0,X0))) ) | ~spl4_1),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f282,f25])).
% 1.52/0.56  fof(f25,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f15])).
% 1.52/0.56  fof(f166,plain,(
% 1.52/0.56    spl4_1 | spl4_2),
% 1.52/0.56    inference(avatar_contradiction_clause,[],[f165])).
% 1.52/0.56  fof(f165,plain,(
% 1.52/0.56    $false | (spl4_1 | spl4_2)),
% 1.52/0.56    inference(subsumption_resolution,[],[f156,f79])).
% 1.52/0.56  fof(f79,plain,(
% 1.52/0.56    r2_hidden(sK2(k2_relat_1(sK1),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | spl4_2),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f74,f26])).
% 1.52/0.56  fof(f74,plain,(
% 1.52/0.56    ~r1_xboole_0(k2_relat_1(sK1),k2_tarski(sK0,sK0)) | spl4_2),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f18,f47,f19])).
% 1.52/0.56  fof(f19,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) = k1_xboole_0) )),
% 1.52/0.56    inference(cnf_transformation,[],[f14])).
% 1.52/0.56  fof(f47,plain,(
% 1.52/0.56    k1_xboole_0 != k10_relat_1(sK1,k2_tarski(sK0,sK0)) | spl4_2),
% 1.52/0.56    inference(avatar_component_clause,[],[f46])).
% 1.52/0.56  fof(f156,plain,(
% 1.52/0.56    ~r2_hidden(sK2(k2_relat_1(sK1),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | (spl4_1 | spl4_2)),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f122,f78,f24])).
% 1.52/0.56  fof(f78,plain,(
% 1.52/0.56    r2_hidden(sK2(k2_relat_1(sK1),k2_tarski(sK0,sK0)),k2_relat_1(sK1)) | spl4_2),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f74,f25])).
% 1.52/0.56  fof(f122,plain,(
% 1.52/0.56    r1_xboole_0(k2_tarski(sK0,sK0),k2_relat_1(sK1)) | spl4_1),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f55,f22])).
% 1.52/0.56  fof(f22,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f3])).
% 1.52/0.56  fof(f55,plain,(
% 1.52/0.56    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_relat_1(sK1)) | spl4_1),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f44,f44,f29])).
% 1.52/0.56  fof(f29,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X1,X2) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f8])).
% 1.52/0.56  fof(f44,plain,(
% 1.52/0.56    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl4_1),
% 1.52/0.56    inference(avatar_component_clause,[],[f42])).
% 1.52/0.56  fof(f50,plain,(
% 1.52/0.56    spl4_1 | ~spl4_2),
% 1.52/0.56    inference(avatar_split_clause,[],[f37,f46,f42])).
% 1.52/0.56  fof(f37,plain,(
% 1.52/0.56    k1_xboole_0 != k10_relat_1(sK1,k2_tarski(sK0,sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 1.52/0.56    inference(definition_unfolding,[],[f16,f21])).
% 1.52/0.56  fof(f21,plain,(
% 1.52/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f4])).
% 1.52/0.56  fof(f4,axiom,(
% 1.52/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.52/0.56  fof(f16,plain,(
% 1.52/0.56    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 1.52/0.56    inference(cnf_transformation,[],[f13])).
% 1.52/0.56  fof(f49,plain,(
% 1.52/0.56    ~spl4_1 | spl4_2),
% 1.52/0.56    inference(avatar_split_clause,[],[f36,f46,f42])).
% 1.52/0.56  fof(f36,plain,(
% 1.52/0.56    k1_xboole_0 = k10_relat_1(sK1,k2_tarski(sK0,sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.52/0.56    inference(definition_unfolding,[],[f17,f21])).
% 1.52/0.56  fof(f17,plain,(
% 1.52/0.56    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.52/0.56    inference(cnf_transformation,[],[f13])).
% 1.52/0.56  % SZS output end Proof for theBenchmark
% 1.52/0.56  % (13120)------------------------------
% 1.52/0.56  % (13120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (13120)Termination reason: Refutation
% 1.52/0.56  
% 1.52/0.56  % (13120)Memory used [KB]: 11001
% 1.52/0.56  % (13120)Time elapsed: 0.145 s
% 1.52/0.56  % (13120)------------------------------
% 1.52/0.56  % (13120)------------------------------
% 1.52/0.56  % (13135)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.52/0.57  % (13110)Success in time 0.201 s
%------------------------------------------------------------------------------
