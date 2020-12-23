%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (  72 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  108 ( 144 expanded)
%              Number of equality atoms :   58 (  84 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f58,f67,f72])).

% (26398)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f72,plain,(
    ~ spl1_3 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl1_3 ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl1_3 ),
    inference(superposition,[],[f21,f66])).

fof(f66,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl1_3
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f21,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).

% (26390)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f16,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f67,plain,
    ( ~ spl1_1
    | spl1_3
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f63,f53,f65,f49])).

fof(f49,plain,
    ( spl1_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f53,plain,
    ( spl1_2
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f63,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_2 ),
    inference(forward_demodulation,[],[f62,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f62,plain,(
    ! [X0] :
      ( k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f61,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f61,plain,(
    ! [X0] :
      ( k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f35,f22])).

fof(f22,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f58,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl1_1 ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f26,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f51,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f56,plain,
    ( ~ spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f47,f53,f49])).

fof(f47,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f45,f23])).

fof(f23,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f28,f43])).

fof(f43,plain,(
    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f42,f24])).

fof(f24,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f42,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(k1_xboole_0,X3)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X3) ) ),
    inference(forward_demodulation,[],[f41,f22])).

fof(f41,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(k1_relat_1(k1_xboole_0),X3)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X3) ) ),
    inference(resolution,[],[f31,f38])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:47:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.52  % (26382)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (26382)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f56,f58,f67,f72])).
% 0.22/0.53  % (26398)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ~spl1_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    $false | ~spl1_3),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | ~spl1_3),
% 0.22/0.53    inference(superposition,[],[f21,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl1_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl1_3 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).
% 0.22/0.53  % (26390)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,negated_conjecture,(
% 0.22/0.53    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.53    inference(negated_conjecture,[],[f10])).
% 0.22/0.53  fof(f10,conjecture,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ~spl1_1 | spl1_3 | ~spl1_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f63,f53,f65,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    spl1_1 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    spl1_2 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_2),
% 0.22/0.53    inference(forward_demodulation,[],[f62,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f53])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f61,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.53    inference(superposition,[],[f35,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f29,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    spl1_1),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    $false | spl1_1),
% 0.22/0.53    inference(resolution,[],[f51,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    v1_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(superposition,[],[f26,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ~v1_relat_1(k1_xboole_0) | spl1_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f49])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ~spl1_1 | spl1_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f47,f53,f49])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(forward_demodulation,[],[f45,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(superposition,[],[f28,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.53    inference(resolution,[],[f42,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X3] : (~r1_xboole_0(k1_xboole_0,X3) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X3)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f41,f22])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X3] : (~r1_xboole_0(k1_relat_1(k1_xboole_0),X3) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X3)) )),
% 0.22/0.53    inference(resolution,[],[f31,f38])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (26382)------------------------------
% 0.22/0.53  % (26382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26382)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (26382)Memory used [KB]: 6140
% 0.22/0.53  % (26382)Time elapsed: 0.110 s
% 0.22/0.53  % (26382)------------------------------
% 0.22/0.53  % (26382)------------------------------
% 0.22/0.54  % (26369)Success in time 0.179 s
%------------------------------------------------------------------------------
