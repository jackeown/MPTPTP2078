%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 123 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  181 ( 395 expanded)
%              Number of equality atoms :   52 (  95 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f684,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f643,f647,f673,f683])).

fof(f683,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK0)
    | sK0 != k3_xboole_0(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    introduced(theory_tautology_sat_conflict,[])).

% (31944)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f673,plain,
    ( spl6_43
    | ~ spl6_2
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f652,f641,f50,f671])).

fof(f671,plain,
    ( spl6_43
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f50,plain,
    ( spl6_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f641,plain,
    ( spl6_39
  <=> sK0 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f652,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0)
    | ~ spl6_2
    | ~ spl6_39 ),
    inference(superposition,[],[f114,f642])).

fof(f642,plain,
    ( sK0 = k3_xboole_0(sK2,sK0)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f641])).

fof(f114,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK2,X0))
    | ~ spl6_2 ),
    inference(resolution,[],[f109,f51])).

fof(f51,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(forward_demodulation,[],[f101,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(superposition,[],[f40,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_xboole_0(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_xboole_0(X0,X1)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f41,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f38,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

% (31945)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (31928)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f647,plain,
    ( spl6_40
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f637,f58,f645])).

fof(f645,plain,
    ( spl6_40
  <=> sK0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f58,plain,
    ( spl6_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f637,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f450,f59])).

fof(f59,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f450,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k3_xboole_0(X2,X3) = X3 ) ),
    inference(global_subsumption,[],[f61,f447])).

fof(f447,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2)
      | k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f44,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK5(X0,X1,X2),X2)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK5(X0,X1,X2),X0)
        & r1_tarski(sK5(X0,X1,X2),X2)
        & r1_tarski(sK5(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK5(X0,X1,X2),X0)
        & r1_tarski(sK5(X0,X1,X2),X2)
        & r1_tarski(sK5(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK5(X0,X1,X2),X0)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f35,f33])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f643,plain,
    ( spl6_39
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f636,f54,f641])).

fof(f54,plain,
    ( spl6_3
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f636,plain,
    ( sK0 = k3_xboole_0(sK2,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f450,f55])).

fof(f55,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f60,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f29,f58])).

fof(f29,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_xboole_0 != sK0
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k1_xboole_0 != sK0
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f56,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f31,f50])).

fof(f31,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f32,f46])).

fof(f46,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f32,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (31933)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (31927)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (31930)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (31942)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (31936)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (31939)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (31943)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (31934)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (31932)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (31929)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (31940)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (31933)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f684,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f643,f647,f673,f683])).
% 0.20/0.50  fof(f683,plain,(
% 0.20/0.50    k1_xboole_0 != k3_xboole_0(sK1,sK0) | sK0 != k3_xboole_0(sK1,sK0) | k1_xboole_0 = sK0),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  % (31944)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  fof(f673,plain,(
% 0.20/0.50    spl6_43 | ~spl6_2 | ~spl6_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f652,f641,f50,f671])).
% 0.20/0.50  fof(f671,plain,(
% 0.20/0.50    spl6_43 <=> k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    spl6_2 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.50  fof(f641,plain,(
% 0.20/0.50    spl6_39 <=> sK0 = k3_xboole_0(sK2,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.20/0.50  fof(f652,plain,(
% 0.20/0.50    k1_xboole_0 = k3_xboole_0(sK1,sK0) | (~spl6_2 | ~spl6_39)),
% 0.20/0.50    inference(superposition,[],[f114,f642])).
% 0.20/0.50  fof(f642,plain,(
% 0.20/0.50    sK0 = k3_xboole_0(sK2,sK0) | ~spl6_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f641])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK2,X0))) ) | ~spl6_2),
% 0.20/0.50    inference(resolution,[],[f109,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    r1_xboole_0(sK1,sK2) | ~spl6_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f50])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f101,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.50    inference(superposition,[],[f40,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(X0,X1) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_xboole_0(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 = k2_xboole_0(X0,X1) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(superposition,[],[f41,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f38,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f2])).
% 0.20/0.50  % (31945)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (31928)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.50  fof(f647,plain,(
% 0.20/0.50    spl6_40 | ~spl6_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f637,f58,f645])).
% 0.20/0.50  fof(f645,plain,(
% 0.20/0.50    spl6_40 <=> sK0 = k3_xboole_0(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl6_4 <=> r1_tarski(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.50  fof(f637,plain,(
% 0.20/0.50    sK0 = k3_xboole_0(sK1,sK0) | ~spl6_4),
% 0.20/0.50    inference(resolution,[],[f450,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    r1_tarski(sK0,sK1) | ~spl6_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f58])).
% 0.20/0.50  fof(f450,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k3_xboole_0(X2,X3) = X3) )),
% 0.20/0.50    inference(global_subsumption,[],[f61,f447])).
% 0.20/0.50  fof(f447,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f446])).
% 0.20/0.50  fof(f446,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2) | k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2)) )),
% 0.20/0.50    inference(resolution,[],[f44,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(sK5(X0,X1,X2),X2) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK5(X0,X1,X2),X0) & r1_tarski(sK5(X0,X1,X2),X2) & r1_tarski(sK5(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK5(X0,X1,X2),X0) & r1_tarski(sK5(X0,X1,X2),X2) & r1_tarski(sK5(X0,X1,X2),X1)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(sK5(X0,X1,X2),X0) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.50    inference(superposition,[],[f35,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.50  fof(f643,plain,(
% 0.20/0.50    spl6_39 | ~spl6_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f636,f54,f641])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    spl6_3 <=> r1_tarski(sK0,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.50  fof(f636,plain,(
% 0.20/0.50    sK0 = k3_xboole_0(sK2,sK0) | ~spl6_3),
% 0.20/0.50    inference(resolution,[],[f450,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    r1_tarski(sK0,sK2) | ~spl6_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f54])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    spl6_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f58])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    r1_tarski(sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    k1_xboole_0 != sK0 & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK2) & r1_tarski(sK0,sK1)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => (k1_xboole_0 != sK0 & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK2) & r1_tarski(sK0,sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (k1_xboole_0 != X0 & (r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    spl6_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f30,f54])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    r1_tarski(sK0,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    spl6_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f31,f50])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    r1_xboole_0(sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ~spl6_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f32,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    spl6_1 <=> k1_xboole_0 = sK0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    k1_xboole_0 != sK0),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (31933)------------------------------
% 0.20/0.50  % (31933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31933)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (31933)Memory used [KB]: 11001
% 0.20/0.50  % (31933)Time elapsed: 0.065 s
% 0.20/0.50  % (31933)------------------------------
% 0.20/0.50  % (31933)------------------------------
% 0.20/0.50  % (31931)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (31924)Success in time 0.141 s
%------------------------------------------------------------------------------
