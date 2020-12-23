%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  78 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 162 expanded)
%              Number of equality atoms :   37 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f82,f136])).

fof(f136,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f45,f20,f32,f128,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | ~ sQ1_eqProxy(X2,X3)
      | ~ r1_tarski(X0,X2)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( sQ1_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).

fof(f128,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f125,f69])).

fof(f69,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f125,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl2_2 ),
    inference(resolution,[],[f124,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sQ1_eqProxy(k7_relat_1(X1,X0),X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f23,f29])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f124,plain,
    ( ~ sQ1_eqProxy(k7_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | spl2_2 ),
    inference(resolution,[],[f114,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sQ1_eqProxy(X1,X0)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f29])).

fof(f114,plain,
    ( ~ sQ1_eqProxy(k1_xboole_0,k7_relat_1(k1_xboole_0,sK0))
    | spl2_2 ),
    inference(resolution,[],[f99,f31])).

fof(f31,plain,(
    sQ1_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(equality_proxy_replacement,[],[f19,f29])).

fof(f19,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f99,plain,
    ( ! [X5] :
        ( ~ sQ1_eqProxy(k1_xboole_0,k2_relat_1(X5))
        | ~ sQ1_eqProxy(X5,k7_relat_1(k1_xboole_0,sK0)) )
    | spl2_2 ),
    inference(resolution,[],[f84,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sQ1_eqProxy(k2_relat_1(X0),k2_relat_1(X1))
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f29])).

fof(f84,plain,
    ( ! [X1] :
        ( ~ sQ1_eqProxy(X1,k2_relat_1(k7_relat_1(k1_xboole_0,sK0)))
        | ~ sQ1_eqProxy(k1_xboole_0,X1) )
    | spl2_2 ),
    inference(resolution,[],[f74,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sQ1_eqProxy(X0,X2)
      | ~ sQ1_eqProxy(X1,X2)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f29])).

fof(f74,plain,
    ( ~ sQ1_eqProxy(k1_xboole_0,k2_relat_1(k7_relat_1(k1_xboole_0,sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_2
  <=> sQ1_eqProxy(k1_xboole_0,k2_relat_1(k7_relat_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f32,plain,(
    sQ1_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(equality_proxy_replacement,[],[f18,f29])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f45,plain,(
    ! [X0] : sQ1_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f29])).

fof(f82,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f35,f77,f46])).

fof(f77,plain,
    ( ! [X0,X1] : ~ sQ1_eqProxy(k2_zfmisc_1(X0,X1),k1_xboole_0)
    | spl2_1 ),
    inference(resolution,[],[f76,f21])).

fof(f21,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f76,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ sQ1_eqProxy(X0,k1_xboole_0) )
    | spl2_1 ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ sQ1_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f29])).

fof(f70,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f35,plain,(
    ! [X0] : sQ1_eqProxy(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(equality_proxy_replacement,[],[f27,f29])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f75,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f56,f72,f68])).

fof(f56,plain,
    ( ~ sQ1_eqProxy(k1_xboole_0,k2_relat_1(k7_relat_1(k1_xboole_0,sK0)))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f50,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sQ1_eqProxy(k2_relat_1(k7_relat_1(X1,X0)),k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f22,f29])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ sQ1_eqProxy(X0,k9_relat_1(k1_xboole_0,sK0))
      | ~ sQ1_eqProxy(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f47,f30])).

fof(f30,plain,(
    ~ sQ1_eqProxy(k1_xboole_0,k9_relat_1(k1_xboole_0,sK0)) ),
    inference(equality_proxy_replacement,[],[f17,f29])).

fof(f17,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (16818)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (16818)Refutation not found, incomplete strategy% (16818)------------------------------
% 0.21/0.47  % (16818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16818)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (16818)Memory used [KB]: 10490
% 0.21/0.47  % (16818)Time elapsed: 0.050 s
% 0.21/0.47  % (16818)------------------------------
% 0.21/0.47  % (16818)------------------------------
% 0.21/0.47  % (16822)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (16828)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (16828)Refutation not found, incomplete strategy% (16828)------------------------------
% 0.21/0.48  % (16828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16828)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (16828)Memory used [KB]: 1535
% 0.21/0.48  % (16828)Time elapsed: 0.058 s
% 0.21/0.48  % (16828)------------------------------
% 0.21/0.48  % (16828)------------------------------
% 0.21/0.48  % (16830)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (16820)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (16829)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (16820)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f75,f82,f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ~spl2_1 | spl2_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f134])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    $false | (~spl2_1 | spl2_2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f45,f20,f32,f128,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | ~sQ1_eqProxy(X2,X3) | ~r1_tarski(X0,X2) | ~sQ1_eqProxy(X0,X1)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X1,X0] : (sQ1_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.49    introduced(equality_proxy_definition,[new_symbols(naming,[sQ1_eqProxy])])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(k1_xboole_0),sK0) | (~spl2_1 | spl2_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f125,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | ~spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl2_1 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(k1_xboole_0),sK0) | ~v1_relat_1(k1_xboole_0) | spl2_2),
% 0.21/0.49    inference(resolution,[],[f124,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sQ1_eqProxy(k7_relat_1(X1,X0),X1) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f23,f29])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~sQ1_eqProxy(k7_relat_1(k1_xboole_0,sK0),k1_xboole_0) | spl2_2),
% 0.21/0.49    inference(resolution,[],[f114,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sQ1_eqProxy(X1,X0) | ~sQ1_eqProxy(X0,X1)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f29])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ~sQ1_eqProxy(k1_xboole_0,k7_relat_1(k1_xboole_0,sK0)) | spl2_2),
% 0.21/0.49    inference(resolution,[],[f99,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    sQ1_eqProxy(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f19,f29])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X5] : (~sQ1_eqProxy(k1_xboole_0,k2_relat_1(X5)) | ~sQ1_eqProxy(X5,k7_relat_1(k1_xboole_0,sK0))) ) | spl2_2),
% 0.21/0.49    inference(resolution,[],[f84,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sQ1_eqProxy(k2_relat_1(X0),k2_relat_1(X1)) | ~sQ1_eqProxy(X0,X1)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f29])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X1] : (~sQ1_eqProxy(X1,k2_relat_1(k7_relat_1(k1_xboole_0,sK0))) | ~sQ1_eqProxy(k1_xboole_0,X1)) ) | spl2_2),
% 0.21/0.49    inference(resolution,[],[f74,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sQ1_eqProxy(X0,X2) | ~sQ1_eqProxy(X1,X2) | ~sQ1_eqProxy(X0,X1)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f29])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~sQ1_eqProxy(k1_xboole_0,k2_relat_1(k7_relat_1(k1_xboole_0,sK0))) | spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl2_2 <=> sQ1_eqProxy(k1_xboole_0,k2_relat_1(k7_relat_1(k1_xboole_0,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    sQ1_eqProxy(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f18,f29])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (sQ1_eqProxy(X0,X0)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f29])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl2_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    $false | spl2_1),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f35,f77,f46])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~sQ1_eqProxy(k2_zfmisc_1(X0,X1),k1_xboole_0)) ) | spl2_1),
% 0.21/0.49    inference(resolution,[],[f76,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~sQ1_eqProxy(X0,k1_xboole_0)) ) | spl2_1),
% 0.21/0.49    inference(resolution,[],[f70,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~v1_relat_1(X0) | ~sQ1_eqProxy(X0,X1)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f29])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ~v1_relat_1(k1_xboole_0) | spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f68])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0] : (sQ1_eqProxy(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0))) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f27,f29])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f72,f68])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ~sQ1_eqProxy(k1_xboole_0,k2_relat_1(k7_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f50,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sQ1_eqProxy(k2_relat_1(k7_relat_1(X1,X0)),k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f22,f29])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0] : (~sQ1_eqProxy(X0,k9_relat_1(k1_xboole_0,sK0)) | ~sQ1_eqProxy(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(resolution,[],[f47,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ~sQ1_eqProxy(k1_xboole_0,k9_relat_1(k1_xboole_0,sK0))),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f17,f29])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (16820)------------------------------
% 0.21/0.50  % (16820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16820)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (16820)Memory used [KB]: 6140
% 0.21/0.50  % (16820)Time elapsed: 0.083 s
% 0.21/0.50  % (16820)------------------------------
% 0.21/0.50  % (16820)------------------------------
% 0.21/0.50  % (16814)Success in time 0.138 s
%------------------------------------------------------------------------------
