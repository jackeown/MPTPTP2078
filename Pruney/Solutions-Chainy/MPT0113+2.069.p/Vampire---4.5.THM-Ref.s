%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:42 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 177 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 ( 461 expanded)
%              Number of equality atoms :   42 (  80 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f990,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f70,f78,f733,f753,f772,f977])).

fof(f977,plain,
    ( spl4_50
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f960,f76,f68,f770])).

fof(f770,plain,
    ( spl4_50
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f68,plain,
    ( spl4_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f76,plain,
    ( spl4_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f960,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f77,f790])).

fof(f790,plain,
    ( ! [X2] : k4_xboole_0(sK0,k4_xboole_0(sK0,X2)) = k4_xboole_0(sK0,k4_xboole_0(sK1,X2))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f777,f197])).

fof(f197,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f46,f73])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(resolution,[],[f41,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f43,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f777,plain,
    ( ! [X2] : k4_xboole_0(sK0,k4_xboole_0(sK1,X2)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,X2)))
    | ~ spl4_5 ),
    inference(superposition,[],[f46,f752])).

fof(f752,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f77,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f772,plain,
    ( ~ spl4_50
    | spl4_2 ),
    inference(avatar_split_clause,[],[f768,f51,f770])).

fof(f51,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f768,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl4_2 ),
    inference(resolution,[],[f52,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f52,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f753,plain,
    ( spl4_5
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f751,f731,f59,f68])).

fof(f59,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f731,plain,
    ( spl4_48
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f751,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f742,f88])).

fof(f88,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f82,f73])).

fof(f82,plain,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(resolution,[],[f35,f65])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f742,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(superposition,[],[f81,f732])).

fof(f732,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f731])).

fof(f81,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0
    | ~ spl4_4 ),
    inference(resolution,[],[f35,f63])).

fof(f63,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f62,f60])).

fof(f60,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f38,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f733,plain,
    ( spl4_48
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f708,f76,f731])).

fof(f708,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl4_6 ),
    inference(superposition,[],[f221,f77])).

fof(f221,plain,(
    ! [X14,X15,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X15,X16))) ),
    inference(superposition,[],[f33,f46])).

fof(f33,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f78,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f71,f55,f76])).

fof(f55,plain,
    ( spl4_3
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f71,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f70,plain,
    ( ~ spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f66,f48,f68])).

fof(f48,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f66,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(resolution,[],[f40,f49])).

fof(f49,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f57,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f53,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f29,f51,f48])).

fof(f29,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:11:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (1828)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.20/0.51  % (1814)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.20/0.52  % (1806)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.52  % (1833)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.20/0.52  % (1829)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.20/0.52  % (1804)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.20/0.52  % (1814)Refutation not found, incomplete strategy% (1814)------------------------------
% 1.20/0.52  % (1814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (1814)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (1814)Memory used [KB]: 10618
% 1.20/0.52  % (1814)Time elapsed: 0.106 s
% 1.20/0.52  % (1814)------------------------------
% 1.20/0.52  % (1814)------------------------------
% 1.20/0.52  % (1805)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.20/0.52  % (1812)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.20/0.53  % (1815)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.20/0.53  % (1807)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.20/0.53  % (1809)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.53  % (1836)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.53  % (1826)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  % (1838)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (1825)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.54  % (1808)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.54  % (1827)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.54  % (1837)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (1810)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.54  % (1827)Refutation not found, incomplete strategy% (1827)------------------------------
% 1.36/0.54  % (1827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (1827)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (1827)Memory used [KB]: 10618
% 1.36/0.54  % (1827)Time elapsed: 0.137 s
% 1.36/0.54  % (1827)------------------------------
% 1.36/0.54  % (1827)------------------------------
% 1.36/0.54  % (1834)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.54  % (1813)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  % (1830)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.55  % (1835)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.55  % (1822)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.55  % (1815)Refutation not found, incomplete strategy% (1815)------------------------------
% 1.36/0.55  % (1815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (1815)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (1815)Memory used [KB]: 10618
% 1.36/0.55  % (1815)Time elapsed: 0.155 s
% 1.36/0.55  % (1815)------------------------------
% 1.36/0.55  % (1815)------------------------------
% 1.36/0.55  % (1816)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.55  % (1832)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.55  % (1811)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.55  % (1832)Refutation not found, incomplete strategy% (1832)------------------------------
% 1.36/0.55  % (1832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (1832)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (1832)Memory used [KB]: 10746
% 1.36/0.55  % (1832)Time elapsed: 0.151 s
% 1.36/0.55  % (1832)------------------------------
% 1.36/0.55  % (1832)------------------------------
% 1.36/0.56  % (1823)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.56  % (1839)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.57  % (1831)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.59  % (1829)Refutation found. Thanks to Tanya!
% 1.36/0.59  % SZS status Theorem for theBenchmark
% 1.36/0.59  % SZS output start Proof for theBenchmark
% 1.36/0.59  fof(f990,plain,(
% 1.36/0.59    $false),
% 1.36/0.59    inference(avatar_sat_refutation,[],[f53,f57,f61,f70,f78,f733,f753,f772,f977])).
% 1.36/0.59  fof(f977,plain,(
% 1.36/0.59    spl4_50 | ~spl4_5 | ~spl4_6),
% 1.36/0.59    inference(avatar_split_clause,[],[f960,f76,f68,f770])).
% 1.36/0.59  fof(f770,plain,(
% 1.36/0.59    spl4_50 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.36/0.59  fof(f68,plain,(
% 1.36/0.59    spl4_5 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.36/0.59  fof(f76,plain,(
% 1.36/0.59    spl4_6 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.36/0.59  fof(f960,plain,(
% 1.36/0.59    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl4_5 | ~spl4_6)),
% 1.36/0.59    inference(superposition,[],[f77,f790])).
% 1.36/0.59  fof(f790,plain,(
% 1.36/0.59    ( ! [X2] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X2)) = k4_xboole_0(sK0,k4_xboole_0(sK1,X2))) ) | ~spl4_5),
% 1.36/0.59    inference(forward_demodulation,[],[f777,f197])).
% 1.36/0.59  fof(f197,plain,(
% 1.36/0.59    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) )),
% 1.36/0.59    inference(superposition,[],[f46,f73])).
% 1.36/0.59  fof(f73,plain,(
% 1.36/0.59    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.36/0.59    inference(resolution,[],[f41,f65])).
% 1.36/0.59  fof(f65,plain,(
% 1.36/0.59    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.36/0.59    inference(duplicate_literal_removal,[],[f64])).
% 1.36/0.59  fof(f64,plain,(
% 1.36/0.59    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.36/0.59    inference(resolution,[],[f39,f38])).
% 1.36/0.59  fof(f38,plain,(
% 1.36/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f26])).
% 1.36/0.59  fof(f26,plain,(
% 1.36/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 1.36/0.59  fof(f25,plain,(
% 1.36/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.36/0.59    introduced(choice_axiom,[])).
% 1.36/0.59  fof(f24,plain,(
% 1.36/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.59    inference(rectify,[],[f23])).
% 1.36/0.59  fof(f23,plain,(
% 1.36/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.59    inference(nnf_transformation,[],[f20])).
% 1.36/0.59  fof(f20,plain,(
% 1.36/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.59    inference(ennf_transformation,[],[f2])).
% 1.36/0.59  fof(f2,axiom,(
% 1.36/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.59  fof(f39,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f26])).
% 1.36/0.59  fof(f41,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f27])).
% 1.36/0.59  fof(f27,plain,(
% 1.36/0.59    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.36/0.59    inference(nnf_transformation,[],[f5])).
% 1.36/0.59  fof(f5,axiom,(
% 1.36/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.36/0.59  fof(f46,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.36/0.59    inference(definition_unfolding,[],[f43,f34])).
% 1.36/0.59  fof(f34,plain,(
% 1.36/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.36/0.59    inference(cnf_transformation,[],[f9])).
% 1.36/0.59  fof(f9,axiom,(
% 1.36/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.36/0.59  fof(f43,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.36/0.59    inference(cnf_transformation,[],[f11])).
% 1.36/0.59  fof(f11,axiom,(
% 1.36/0.59    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.36/0.59  fof(f777,plain,(
% 1.36/0.59    ( ! [X2] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X2)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,X2)))) ) | ~spl4_5),
% 1.36/0.59    inference(superposition,[],[f46,f752])).
% 1.36/0.59  fof(f752,plain,(
% 1.36/0.59    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl4_5),
% 1.36/0.59    inference(avatar_component_clause,[],[f68])).
% 1.36/0.59  fof(f77,plain,(
% 1.36/0.59    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl4_6),
% 1.36/0.59    inference(avatar_component_clause,[],[f76])).
% 1.36/0.59  fof(f772,plain,(
% 1.36/0.59    ~spl4_50 | spl4_2),
% 1.36/0.59    inference(avatar_split_clause,[],[f768,f51,f770])).
% 1.36/0.59  fof(f51,plain,(
% 1.36/0.59    spl4_2 <=> r1_xboole_0(sK0,sK2)),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.36/0.59  fof(f768,plain,(
% 1.36/0.59    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl4_2),
% 1.36/0.59    inference(resolution,[],[f52,f44])).
% 1.36/0.59  fof(f44,plain,(
% 1.36/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.36/0.59    inference(definition_unfolding,[],[f36,f34])).
% 1.36/0.59  fof(f36,plain,(
% 1.36/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.36/0.59    inference(cnf_transformation,[],[f19])).
% 1.36/0.59  fof(f19,plain,(
% 1.36/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 1.36/0.59    inference(ennf_transformation,[],[f14])).
% 1.36/0.59  fof(f14,plain,(
% 1.36/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 1.36/0.59    inference(unused_predicate_definition_removal,[],[f3])).
% 1.36/0.59  fof(f3,axiom,(
% 1.36/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.36/0.59  fof(f52,plain,(
% 1.36/0.59    ~r1_xboole_0(sK0,sK2) | spl4_2),
% 1.36/0.59    inference(avatar_component_clause,[],[f51])).
% 1.36/0.59  fof(f753,plain,(
% 1.36/0.59    spl4_5 | ~spl4_4 | ~spl4_48),
% 1.36/0.59    inference(avatar_split_clause,[],[f751,f731,f59,f68])).
% 1.36/0.59  fof(f59,plain,(
% 1.36/0.59    spl4_4 <=> v1_xboole_0(k1_xboole_0)),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.36/0.59  fof(f731,plain,(
% 1.36/0.59    spl4_48 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 1.36/0.59  fof(f751,plain,(
% 1.36/0.59    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl4_4 | ~spl4_48)),
% 1.36/0.59    inference(forward_demodulation,[],[f742,f88])).
% 1.36/0.59  fof(f88,plain,(
% 1.36/0.59    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.36/0.59    inference(forward_demodulation,[],[f82,f73])).
% 1.36/0.59  fof(f82,plain,(
% 1.36/0.59    ( ! [X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 1.36/0.59    inference(resolution,[],[f35,f65])).
% 1.36/0.59  fof(f35,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 1.36/0.59    inference(cnf_transformation,[],[f18])).
% 1.36/0.59  fof(f18,plain,(
% 1.36/0.59    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.36/0.59    inference(ennf_transformation,[],[f7])).
% 1.36/0.59  fof(f7,axiom,(
% 1.36/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.36/0.59  fof(f742,plain,(
% 1.36/0.59    k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_48)),
% 1.36/0.59    inference(superposition,[],[f81,f732])).
% 1.36/0.59  fof(f732,plain,(
% 1.36/0.59    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl4_48),
% 1.36/0.59    inference(avatar_component_clause,[],[f731])).
% 1.36/0.59  fof(f81,plain,(
% 1.36/0.59    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) ) | ~spl4_4),
% 1.36/0.59    inference(resolution,[],[f35,f63])).
% 1.36/0.59  fof(f63,plain,(
% 1.36/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_4),
% 1.36/0.59    inference(resolution,[],[f62,f60])).
% 1.36/0.59  fof(f60,plain,(
% 1.36/0.59    v1_xboole_0(k1_xboole_0) | ~spl4_4),
% 1.36/0.59    inference(avatar_component_clause,[],[f59])).
% 1.36/0.59  fof(f62,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 1.36/0.59    inference(resolution,[],[f38,f32])).
% 1.36/0.59  fof(f32,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f17])).
% 1.36/0.59  fof(f17,plain,(
% 1.36/0.59    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.36/0.59    inference(ennf_transformation,[],[f15])).
% 1.36/0.59  fof(f15,plain,(
% 1.36/0.59    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.59    inference(unused_predicate_definition_removal,[],[f1])).
% 1.36/0.59  fof(f1,axiom,(
% 1.36/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.36/0.59  fof(f733,plain,(
% 1.36/0.59    spl4_48 | ~spl4_6),
% 1.36/0.59    inference(avatar_split_clause,[],[f708,f76,f731])).
% 1.36/0.59  fof(f708,plain,(
% 1.36/0.59    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl4_6),
% 1.36/0.59    inference(superposition,[],[f221,f77])).
% 1.36/0.59  fof(f221,plain,(
% 1.36/0.59    ( ! [X14,X15,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X15,X16)))) )),
% 1.36/0.59    inference(superposition,[],[f33,f46])).
% 1.36/0.59  fof(f33,plain,(
% 1.36/0.59    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.36/0.59    inference(cnf_transformation,[],[f8])).
% 1.36/0.59  fof(f8,axiom,(
% 1.36/0.59    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.36/0.59  fof(f78,plain,(
% 1.36/0.59    spl4_6 | ~spl4_3),
% 1.36/0.59    inference(avatar_split_clause,[],[f71,f55,f76])).
% 1.36/0.59  fof(f55,plain,(
% 1.36/0.59    spl4_3 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.36/0.59  fof(f71,plain,(
% 1.36/0.59    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl4_3),
% 1.36/0.59    inference(resolution,[],[f41,f56])).
% 1.36/0.59  fof(f56,plain,(
% 1.36/0.59    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl4_3),
% 1.36/0.59    inference(avatar_component_clause,[],[f55])).
% 1.36/0.59  fof(f70,plain,(
% 1.36/0.59    ~spl4_5 | spl4_1),
% 1.36/0.59    inference(avatar_split_clause,[],[f66,f48,f68])).
% 1.36/0.59  fof(f48,plain,(
% 1.36/0.59    spl4_1 <=> r1_tarski(sK0,sK1)),
% 1.36/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.36/0.59  fof(f66,plain,(
% 1.36/0.59    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl4_1),
% 1.36/0.59    inference(resolution,[],[f40,f49])).
% 1.36/0.59  fof(f49,plain,(
% 1.36/0.59    ~r1_tarski(sK0,sK1) | spl4_1),
% 1.36/0.59    inference(avatar_component_clause,[],[f48])).
% 1.36/0.59  fof(f40,plain,(
% 1.36/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f27])).
% 1.36/0.59  fof(f61,plain,(
% 1.36/0.59    spl4_4),
% 1.36/0.59    inference(avatar_split_clause,[],[f30,f59])).
% 1.36/0.59  fof(f30,plain,(
% 1.36/0.59    v1_xboole_0(k1_xboole_0)),
% 1.36/0.59    inference(cnf_transformation,[],[f4])).
% 1.36/0.59  fof(f4,axiom,(
% 1.36/0.59    v1_xboole_0(k1_xboole_0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.36/0.59  fof(f57,plain,(
% 1.36/0.59    spl4_3),
% 1.36/0.59    inference(avatar_split_clause,[],[f28,f55])).
% 1.36/0.59  fof(f28,plain,(
% 1.36/0.59    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.59    inference(cnf_transformation,[],[f22])).
% 1.36/0.59  fof(f22,plain,(
% 1.36/0.59    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21])).
% 1.36/0.59  fof(f21,plain,(
% 1.36/0.59    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.36/0.59    introduced(choice_axiom,[])).
% 1.36/0.59  fof(f16,plain,(
% 1.36/0.59    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.36/0.59    inference(ennf_transformation,[],[f13])).
% 1.36/0.59  fof(f13,negated_conjecture,(
% 1.36/0.59    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.36/0.59    inference(negated_conjecture,[],[f12])).
% 1.36/0.59  fof(f12,conjecture,(
% 1.36/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.36/0.59  fof(f53,plain,(
% 1.36/0.59    ~spl4_1 | ~spl4_2),
% 1.36/0.59    inference(avatar_split_clause,[],[f29,f51,f48])).
% 1.36/0.59  fof(f29,plain,(
% 1.36/0.59    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.36/0.59    inference(cnf_transformation,[],[f22])).
% 1.36/0.59  % SZS output end Proof for theBenchmark
% 1.36/0.59  % (1829)------------------------------
% 1.36/0.59  % (1829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.59  % (1829)Termination reason: Refutation
% 1.36/0.59  
% 1.36/0.59  % (1829)Memory used [KB]: 11641
% 1.36/0.59  % (1829)Time elapsed: 0.195 s
% 1.36/0.59  % (1829)------------------------------
% 1.36/0.59  % (1829)------------------------------
% 1.36/0.60  % (1803)Success in time 0.229 s
%------------------------------------------------------------------------------
