%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:00 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 143 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  185 ( 336 expanded)
%              Number of equality atoms :   41 (  82 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f185,f209,f228,f241,f248,f391])).

fof(f391,plain,
    ( ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f385])).

fof(f385,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f73,f293])).

fof(f293,plain,
    ( k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f290,f184])).

fof(f184,plain,
    ( k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl3_3
  <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f290,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f199,f240])).

fof(f240,plain,
    ( k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl3_7
  <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f199,plain,(
    ! [X23,X22] : k2_wellord1(k2_wellord1(sK2,X22),X23) = k7_relat_1(k8_relat_1(X23,k2_wellord1(sK2,X22)),X23) ),
    inference(resolution,[],[f52,f30])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(f52,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_relat_1(X6)
      | k2_wellord1(k2_wellord1(X6,X7),X8) = k7_relat_1(k8_relat_1(X8,k2_wellord1(X6,X7)),X8) ) ),
    inference(resolution,[],[f39,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

fof(f73,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(superposition,[],[f32,f71])).

fof(f71,plain,(
    ! [X19,X18] : k2_wellord1(k2_wellord1(sK2,X18),X19) = k2_wellord1(k2_wellord1(sK2,X19),X18) ),
    inference(resolution,[],[f42,f30])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(f32,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f248,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f242,f30])).

fof(f242,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(resolution,[],[f188,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f188,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_4
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f241,plain,
    ( ~ spl3_4
    | ~ spl3_2
    | spl3_7 ),
    inference(avatar_split_clause,[],[f231,f239,f180,f187])).

fof(f180,plain,
    ( spl3_2
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f231,plain,
    ( k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f109,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0)),X0)
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f36,f47])).

fof(f47,plain,(
    ! [X9] : k2_wellord1(sK2,X9) = k8_relat_1(X9,k7_relat_1(sK2,X9)) ),
    inference(resolution,[],[f38,f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f109,plain,(
    ! [X12] :
      ( ~ r1_tarski(k2_relat_1(X12),sK0)
      | k8_relat_1(sK1,X12) = X12
      | ~ v1_relat_1(X12) ) ),
    inference(resolution,[],[f62,f31])).

fof(f31,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),X4)
      | ~ r1_tarski(X4,X3)
      | k8_relat_1(X3,X2) = X2
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f41,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f228,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f219,f30])).

fof(f219,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(resolution,[],[f181,f35])).

fof(f181,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f180])).

fof(f209,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f200,f30])).

fof(f200,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f178,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f178,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl3_1
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f185,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f172,f183,f180,f177])).

fof(f172,plain,
    ( k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f97,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k2_wellord1(sK2,X0)),X0)
      | ~ v1_relat_1(k8_relat_1(X0,sK2)) ) ),
    inference(superposition,[],[f37,f53])).

fof(f53,plain,(
    ! [X9] : k2_wellord1(sK2,X9) = k7_relat_1(k8_relat_1(X9,sK2),X9) ),
    inference(resolution,[],[f39,f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f97,plain,(
    ! [X12] :
      ( ~ r1_tarski(k1_relat_1(X12),sK0)
      | k7_relat_1(X12,sK1) = X12
      | ~ v1_relat_1(X12) ) ),
    inference(resolution,[],[f57,f31])).

fof(f57,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X2),X4)
      | ~ r1_tarski(X4,X3)
      | k7_relat_1(X2,X3) = X2
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f40,f43])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:59:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.47  % (21448)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.48  % (21453)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.48  % (21454)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.48  % (21461)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.48  % (21458)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.48  % (21457)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.48  % (21450)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.49  % (21472)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.49  % (21467)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.19/0.49  % (21463)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.49  % (21452)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.49  % (21469)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.19/0.49  % (21464)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.49  % (21468)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.50  % (21449)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.50  % (21472)Refutation not found, incomplete strategy% (21472)------------------------------
% 0.19/0.50  % (21472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (21472)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (21472)Memory used [KB]: 10618
% 0.19/0.50  % (21472)Time elapsed: 0.055 s
% 0.19/0.50  % (21472)------------------------------
% 0.19/0.50  % (21472)------------------------------
% 0.19/0.50  % (21451)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.19/0.50  % (21456)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.50  % (21459)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.19/0.50  % (21471)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.19/0.51  % (21460)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.19/0.51  % (21462)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.51  % (21466)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.19/0.51  % (21470)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.19/0.52  % (21465)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.19/0.52  % (21461)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f392,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f185,f209,f228,f241,f248,f391])).
% 0.19/0.52  fof(f391,plain,(
% 0.19/0.52    ~spl3_3 | ~spl3_7),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f390])).
% 0.19/0.52  fof(f390,plain,(
% 0.19/0.52    $false | (~spl3_3 | ~spl3_7)),
% 0.19/0.52    inference(trivial_inequality_removal,[],[f385])).
% 0.19/0.52  fof(f385,plain,(
% 0.19/0.52    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) | (~spl3_3 | ~spl3_7)),
% 0.19/0.52    inference(superposition,[],[f73,f293])).
% 0.19/0.52  fof(f293,plain,(
% 0.19/0.52    k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) | (~spl3_3 | ~spl3_7)),
% 0.19/0.52    inference(forward_demodulation,[],[f290,f184])).
% 0.19/0.52  fof(f184,plain,(
% 0.19/0.52    k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~spl3_3),
% 0.19/0.52    inference(avatar_component_clause,[],[f183])).
% 0.19/0.52  fof(f183,plain,(
% 0.19/0.52    spl3_3 <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.52  fof(f290,plain,(
% 0.19/0.52    k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~spl3_7),
% 0.19/0.52    inference(superposition,[],[f199,f240])).
% 0.19/0.52  fof(f240,plain,(
% 0.19/0.52    k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~spl3_7),
% 0.19/0.52    inference(avatar_component_clause,[],[f239])).
% 0.19/0.52  fof(f239,plain,(
% 0.19/0.52    spl3_7 <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.52  fof(f199,plain,(
% 0.19/0.52    ( ! [X23,X22] : (k2_wellord1(k2_wellord1(sK2,X22),X23) = k7_relat_1(k8_relat_1(X23,k2_wellord1(sK2,X22)),X23)) )),
% 0.19/0.52    inference(resolution,[],[f52,f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    v1_relat_1(sK2)),
% 0.19/0.52    inference(cnf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.19/0.52    inference(flattening,[],[f14])).
% 0.19/0.52  fof(f14,plain,(
% 0.19/0.52    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.19/0.52    inference(ennf_transformation,[],[f13])).
% 0.19/0.52  fof(f13,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.19/0.52    inference(negated_conjecture,[],[f12])).
% 0.19/0.52  fof(f12,conjecture,(
% 0.19/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).
% 0.19/0.52  fof(f52,plain,(
% 0.19/0.52    ( ! [X6,X8,X7] : (~v1_relat_1(X6) | k2_wellord1(k2_wellord1(X6,X7),X8) = k7_relat_1(k8_relat_1(X8,k2_wellord1(X6,X7)),X8)) )),
% 0.19/0.52    inference(resolution,[],[f39,f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f18])).
% 0.19/0.52  fof(f18,plain,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f9])).
% 0.19/0.52  fof(f9,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).
% 0.19/0.52  fof(f73,plain,(
% 0.19/0.52    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 0.19/0.52    inference(superposition,[],[f32,f71])).
% 0.19/0.52  fof(f71,plain,(
% 0.19/0.52    ( ! [X19,X18] : (k2_wellord1(k2_wellord1(sK2,X18),X19) = k2_wellord1(k2_wellord1(sK2,X19),X18)) )),
% 0.19/0.52    inference(resolution,[],[f42,f30])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 0.19/0.52    inference(ennf_transformation,[],[f11])).
% 0.19/0.52  fof(f11,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 0.19/0.52    inference(cnf_transformation,[],[f15])).
% 0.19/0.52  fof(f248,plain,(
% 0.19/0.52    spl3_4),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f247])).
% 0.19/0.52  fof(f247,plain,(
% 0.19/0.52    $false | spl3_4),
% 0.19/0.52    inference(resolution,[],[f242,f30])).
% 0.19/0.52  fof(f242,plain,(
% 0.19/0.52    ~v1_relat_1(sK2) | spl3_4),
% 0.19/0.52    inference(resolution,[],[f188,f33])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f16])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.19/0.52  fof(f188,plain,(
% 0.19/0.52    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_4),
% 0.19/0.52    inference(avatar_component_clause,[],[f187])).
% 0.19/0.52  fof(f187,plain,(
% 0.19/0.52    spl3_4 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.52  fof(f241,plain,(
% 0.19/0.52    ~spl3_4 | ~spl3_2 | spl3_7),
% 0.19/0.52    inference(avatar_split_clause,[],[f231,f239,f180,f187])).
% 0.19/0.52  fof(f180,plain,(
% 0.19/0.52    spl3_2 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.52  fof(f231,plain,(
% 0.19/0.52    k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.19/0.52    inference(resolution,[],[f109,f48])).
% 0.19/0.52  fof(f48,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(k2_wellord1(sK2,X0)),X0) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.19/0.52    inference(superposition,[],[f36,f47])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    ( ! [X9] : (k2_wellord1(sK2,X9) = k8_relat_1(X9,k7_relat_1(sK2,X9))) )),
% 0.19/0.52    inference(resolution,[],[f38,f30])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f19])).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.19/0.52  fof(f109,plain,(
% 0.19/0.52    ( ! [X12] : (~r1_tarski(k2_relat_1(X12),sK0) | k8_relat_1(sK1,X12) = X12 | ~v1_relat_1(X12)) )),
% 0.19/0.52    inference(resolution,[],[f62,f31])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    r1_tarski(sK0,sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f15])).
% 0.19/0.52  fof(f62,plain,(
% 0.19/0.52    ( ! [X4,X2,X3] : (~r1_tarski(k2_relat_1(X2),X4) | ~r1_tarski(X4,X3) | k8_relat_1(X3,X2) = X2 | ~v1_relat_1(X2)) )),
% 0.19/0.52    inference(resolution,[],[f41,f43])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.52    inference(flattening,[],[f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f25])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.19/0.52  fof(f228,plain,(
% 0.19/0.52    spl3_2),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f227])).
% 0.19/0.52  fof(f227,plain,(
% 0.19/0.52    $false | spl3_2),
% 0.19/0.52    inference(resolution,[],[f219,f30])).
% 0.19/0.52  fof(f219,plain,(
% 0.19/0.52    ~v1_relat_1(sK2) | spl3_2),
% 0.19/0.52    inference(resolution,[],[f181,f35])).
% 0.19/0.52  fof(f181,plain,(
% 0.19/0.52    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_2),
% 0.19/0.52    inference(avatar_component_clause,[],[f180])).
% 0.19/0.52  fof(f209,plain,(
% 0.19/0.52    spl3_1),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f208])).
% 0.19/0.52  fof(f208,plain,(
% 0.19/0.52    $false | spl3_1),
% 0.19/0.52    inference(resolution,[],[f200,f30])).
% 0.19/0.52  fof(f200,plain,(
% 0.19/0.52    ~v1_relat_1(sK2) | spl3_1),
% 0.19/0.52    inference(resolution,[],[f178,f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f17])).
% 0.19/0.52  fof(f17,plain,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.19/0.52  fof(f178,plain,(
% 0.19/0.52    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl3_1),
% 0.19/0.52    inference(avatar_component_clause,[],[f177])).
% 0.19/0.52  fof(f177,plain,(
% 0.19/0.52    spl3_1 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.52  fof(f185,plain,(
% 0.19/0.52    ~spl3_1 | ~spl3_2 | spl3_3),
% 0.19/0.52    inference(avatar_split_clause,[],[f172,f183,f180,f177])).
% 0.19/0.52  fof(f172,plain,(
% 0.19/0.52    k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.19/0.52    inference(resolution,[],[f97,f59])).
% 0.19/0.52  fof(f59,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k1_relat_1(k2_wellord1(sK2,X0)),X0) | ~v1_relat_1(k8_relat_1(X0,sK2))) )),
% 0.19/0.52    inference(superposition,[],[f37,f53])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    ( ! [X9] : (k2_wellord1(sK2,X9) = k7_relat_1(k8_relat_1(X9,sK2),X9)) )),
% 0.19/0.52    inference(resolution,[],[f39,f30])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f20])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.19/0.52  fof(f97,plain,(
% 0.19/0.52    ( ! [X12] : (~r1_tarski(k1_relat_1(X12),sK0) | k7_relat_1(X12,sK1) = X12 | ~v1_relat_1(X12)) )),
% 0.19/0.52    inference(resolution,[],[f57,f31])).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    ( ! [X4,X2,X3] : (~r1_tarski(k1_relat_1(X2),X4) | ~r1_tarski(X4,X3) | k7_relat_1(X2,X3) = X2 | ~v1_relat_1(X2)) )),
% 0.19/0.52    inference(resolution,[],[f40,f43])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (21461)------------------------------
% 0.19/0.52  % (21461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (21461)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (21461)Memory used [KB]: 11001
% 0.19/0.52  % (21461)Time elapsed: 0.111 s
% 0.19/0.52  % (21461)------------------------------
% 0.19/0.52  % (21461)------------------------------
% 0.19/0.52  % (21445)Success in time 0.172 s
%------------------------------------------------------------------------------
