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
% DateTime   : Thu Dec  3 12:43:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 (  89 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 212 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f1177,f1197,f1220])).

fof(f1220,plain,
    ( ~ spl6_2
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f1209])).

fof(f1209,plain,
    ( $false
    | ~ spl6_2
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f185,f59,f1176,f112])).

fof(f112,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(X6,k2_zfmisc_1(X7,X4))
      | r1_tarski(X6,k2_zfmisc_1(X7,X5))
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f42,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f1176,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5)))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f1174])).

fof(f1174,plain,
    ( spl6_9
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f59,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f185,plain,(
    ! [X19,X18] : r1_tarski(X18,k2_xboole_0(X19,X18)) ),
    inference(forward_demodulation,[],[f183,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f183,plain,(
    ! [X19,X18] : r1_tarski(X18,k2_xboole_0(X19,k5_xboole_0(X18,k3_xboole_0(X18,X19)))) ),
    inference(resolution,[],[f47,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f35,f46])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1197,plain,
    ( ~ spl6_1
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f1184])).

fof(f1184,plain,
    ( $false
    | ~ spl6_1
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f54,f285,f1172,f40])).

fof(f1172,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5)))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f1170])).

fof(f1170,plain,
    ( spl6_8
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f285,plain,(
    ! [X17,X15,X16] : r1_tarski(k2_zfmisc_1(X15,X16),k2_zfmisc_1(X15,k2_xboole_0(X16,X17))) ),
    inference(superposition,[],[f39,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f54,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl6_1
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1177,plain,
    ( ~ spl6_8
    | ~ spl6_9
    | spl6_3 ),
    inference(avatar_split_clause,[],[f1143,f62,f1174,f1170])).

fof(f62,plain,
    ( spl6_3
  <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1143,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5)))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5)))
    | spl6_3 ),
    inference(resolution,[],[f229,f64])).

fof(f64,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f229,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X3,X4),k2_zfmisc_1(k2_xboole_0(X0,X2),X1))
      | ~ r1_tarski(X4,k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f34,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f65,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f60,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f32,f57])).

fof(f32,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f31,f52])).

fof(f31,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:34:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (12849)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (12845)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (12859)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (12867)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (12844)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (12846)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (12870)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (12853)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (12872)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (12848)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (12873)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (12847)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (12855)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (12850)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (12861)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (12856)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (12864)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (12871)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (12863)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (12854)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (12858)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (12862)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (12866)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (12868)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (12857)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (12852)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (12860)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (12865)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (12869)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (12851)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.59  % (12867)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f1221,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(avatar_sat_refutation,[],[f55,f60,f65,f1177,f1197,f1220])).
% 0.20/0.59  fof(f1220,plain,(
% 0.20/0.59    ~spl6_2 | spl6_9),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f1209])).
% 0.20/0.59  fof(f1209,plain,(
% 0.20/0.59    $false | (~spl6_2 | spl6_9)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f185,f59,f1176,f112])).
% 0.20/0.59  fof(f112,plain,(
% 0.20/0.59    ( ! [X6,X4,X7,X5] : (~r1_tarski(X6,k2_zfmisc_1(X7,X4)) | r1_tarski(X6,k2_zfmisc_1(X7,X5)) | ~r1_tarski(X4,X5)) )),
% 0.20/0.59    inference(resolution,[],[f42,f40])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f25])).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.59    inference(flattening,[],[f24])).
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.59    inference(ennf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.59  fof(f42,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f26])).
% 0.20/0.59  fof(f26,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f15])).
% 0.20/0.59  fof(f15,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.20/0.59  fof(f1176,plain,(
% 0.20/0.59    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5))) | spl6_9),
% 0.20/0.59    inference(avatar_component_clause,[],[f1174])).
% 0.20/0.59  fof(f1174,plain,(
% 0.20/0.59    spl6_9 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5)))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.59  fof(f59,plain,(
% 0.20/0.59    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | ~spl6_2),
% 0.20/0.59    inference(avatar_component_clause,[],[f57])).
% 0.20/0.59  fof(f57,plain,(
% 0.20/0.59    spl6_2 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.59  fof(f185,plain,(
% 0.20/0.59    ( ! [X19,X18] : (r1_tarski(X18,k2_xboole_0(X19,X18))) )),
% 0.20/0.59    inference(forward_demodulation,[],[f183,f48])).
% 0.20/0.59  fof(f48,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f38,f46])).
% 0.20/0.59  fof(f46,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.59  fof(f38,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.59  fof(f183,plain,(
% 0.20/0.59    ( ! [X19,X18] : (r1_tarski(X18,k2_xboole_0(X19,k5_xboole_0(X18,k3_xboole_0(X18,X19))))) )),
% 0.20/0.59    inference(resolution,[],[f47,f49])).
% 0.20/0.59  fof(f49,plain,(
% 0.20/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.59    inference(equality_resolution,[],[f44])).
% 0.20/0.59  fof(f44,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.59    inference(cnf_transformation,[],[f30])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.59    inference(flattening,[],[f29])).
% 0.20/0.59  fof(f29,plain,(
% 0.20/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.59    inference(nnf_transformation,[],[f1])).
% 0.20/0.59  fof(f1,axiom,(
% 0.20/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.59  fof(f47,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f35,f46])).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f23])).
% 0.20/0.59  fof(f23,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.59    inference(ennf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.20/0.59  fof(f1197,plain,(
% 0.20/0.59    ~spl6_1 | spl6_8),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f1184])).
% 0.20/0.59  fof(f1184,plain,(
% 0.20/0.59    $false | (~spl6_1 | spl6_8)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f54,f285,f1172,f40])).
% 0.20/0.59  fof(f1172,plain,(
% 0.20/0.59    ~r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5))) | spl6_8),
% 0.20/0.59    inference(avatar_component_clause,[],[f1170])).
% 0.20/0.59  fof(f1170,plain,(
% 0.20/0.59    spl6_8 <=> r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5)))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.59  fof(f285,plain,(
% 0.20/0.59    ( ! [X17,X15,X16] : (r1_tarski(k2_zfmisc_1(X15,X16),k2_zfmisc_1(X15,k2_xboole_0(X16,X17)))) )),
% 0.20/0.59    inference(superposition,[],[f39,f37])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f16])).
% 0.20/0.59  fof(f16,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.20/0.59  fof(f39,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f7])).
% 0.20/0.59  fof(f7,axiom,(
% 0.20/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) | ~spl6_1),
% 0.20/0.59    inference(avatar_component_clause,[],[f52])).
% 0.20/0.59  fof(f52,plain,(
% 0.20/0.59    spl6_1 <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.59  fof(f1177,plain,(
% 0.20/0.59    ~spl6_8 | ~spl6_9 | spl6_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f1143,f62,f1174,f1170])).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    spl6_3 <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.59  fof(f1143,plain,(
% 0.20/0.59    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5))) | ~r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5))) | spl6_3),
% 0.20/0.59    inference(resolution,[],[f229,f64])).
% 0.20/0.59  fof(f64,plain,(
% 0.20/0.59    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | spl6_3),
% 0.20/0.59    inference(avatar_component_clause,[],[f62])).
% 0.20/0.59  fof(f229,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X3,X4),k2_zfmisc_1(k2_xboole_0(X0,X2),X1)) | ~r1_tarski(X4,k2_zfmisc_1(X2,X1)) | ~r1_tarski(X3,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.59    inference(superposition,[],[f34,f36])).
% 0.20/0.59  fof(f36,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f16])).
% 0.20/0.59  fof(f34,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f22])).
% 0.20/0.59  fof(f22,plain,(
% 0.20/0.59    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.20/0.59    inference(flattening,[],[f21])).
% 0.20/0.59  fof(f21,plain,(
% 0.20/0.59    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.20/0.59    inference(ennf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 0.20/0.59  fof(f65,plain,(
% 0.20/0.59    ~spl6_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f33,f62])).
% 0.20/0.59  fof(f33,plain,(
% 0.20/0.59    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.20/0.59    inference(cnf_transformation,[],[f28])).
% 0.20/0.59  fof(f28,plain,(
% 0.20/0.59    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f27])).
% 0.20/0.59  fof(f27,plain,(
% 0.20/0.59    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 0.20/0.59    inference(flattening,[],[f19])).
% 0.20/0.59  fof(f19,plain,(
% 0.20/0.59    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 0.20/0.59    inference(ennf_transformation,[],[f18])).
% 0.20/0.59  fof(f18,negated_conjecture,(
% 0.20/0.59    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.20/0.59    inference(negated_conjecture,[],[f17])).
% 0.20/0.59  fof(f17,conjecture,(
% 0.20/0.59    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 0.20/0.59  fof(f60,plain,(
% 0.20/0.59    spl6_2),
% 0.20/0.59    inference(avatar_split_clause,[],[f32,f57])).
% 0.20/0.59  fof(f32,plain,(
% 0.20/0.59    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.20/0.59    inference(cnf_transformation,[],[f28])).
% 0.20/0.59  fof(f55,plain,(
% 0.20/0.59    spl6_1),
% 0.20/0.59    inference(avatar_split_clause,[],[f31,f52])).
% 0.20/0.59  fof(f31,plain,(
% 0.20/0.59    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.20/0.59    inference(cnf_transformation,[],[f28])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (12867)------------------------------
% 0.20/0.59  % (12867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (12867)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (12867)Memory used [KB]: 11641
% 0.20/0.59  % (12867)Time elapsed: 0.153 s
% 0.20/0.59  % (12867)------------------------------
% 0.20/0.59  % (12867)------------------------------
% 1.87/0.59  % (12843)Success in time 0.242 s
%------------------------------------------------------------------------------
