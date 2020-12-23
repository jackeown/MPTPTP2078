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
% DateTime   : Thu Dec  3 12:37:40 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 112 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  157 ( 278 expanded)
%              Number of equality atoms :   32 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1008,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f110,f138,f804,f855,f963,f984,f1007])).

fof(f1007,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f999])).

fof(f999,plain,
    ( $false
    | ~ spl5_1
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f108,f56,f61,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f61,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_1
  <=> r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f56,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k1_enumset1(X4,X1,X2)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f108,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_5
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f984,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f979])).

fof(f979,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f858,f964,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f964,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_1
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f877,f799])).

fof(f799,plain,
    ( sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f797])).

fof(f797,plain,
    ( spl5_8
  <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f877,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),sK2)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f60,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,
    ( ~ r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f858,plain,
    ( r1_tarski(k1_tarski(sK1),sK2)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f65,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f963,plain,
    ( spl5_1
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f948])).

fof(f948,plain,
    ( $false
    | spl5_1
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f113,f880,f25])).

fof(f880,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_1
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f877,f803])).

fof(f803,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f801])).

fof(f801,plain,
    ( spl5_9
  <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f113,plain,
    ( r1_tarski(k1_tarski(sK0),sK2)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f109,f24])).

fof(f109,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f855,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f845])).

fof(f845,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f64,f52,f61,f26])).

fof(f52,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k1_enumset1(X0,X1,X4)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f804,plain,
    ( spl5_8
    | spl5_9
    | spl5_1 ),
    inference(avatar_split_clause,[],[f291,f59,f801,f797])).

fof(f291,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | spl5_1 ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)
    | spl5_1 ),
    inference(resolution,[],[f145,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f145,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f60,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f138,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f46,f107,f63,f59])).

fof(f46,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f21,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f110,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f45,f107,f59])).

fof(f45,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f22,f34])).

fof(f22,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f44,f63,f59])).

fof(f44,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f23,f34])).

fof(f23,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:52:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (26183)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (26158)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (26153)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (26156)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (26175)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (26176)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (26160)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (26162)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (26168)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (26157)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.53  % (26161)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.30/0.53  % (26159)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.53  % (26167)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.30/0.53  % (26163)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.53  % (26173)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.30/0.54  % (26165)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.54  % (26169)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.30/0.54  % (26154)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.54  % (26172)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.54  % (26177)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.54  % (26155)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.55  % (26181)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (26164)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (26170)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (26180)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.55  % (26179)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.55  % (26174)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (26182)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.56  % (26171)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.56  % (26171)Refutation not found, incomplete strategy% (26171)------------------------------
% 1.41/0.56  % (26171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (26171)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (26171)Memory used [KB]: 10618
% 1.41/0.56  % (26171)Time elapsed: 0.152 s
% 1.41/0.56  % (26171)------------------------------
% 1.41/0.56  % (26171)------------------------------
% 1.41/0.56  % (26178)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.58  % (26157)Refutation found. Thanks to Tanya!
% 1.41/0.58  % SZS status Theorem for theBenchmark
% 1.41/0.58  % SZS output start Proof for theBenchmark
% 1.41/0.58  fof(f1008,plain,(
% 1.41/0.58    $false),
% 1.41/0.58    inference(avatar_sat_refutation,[],[f66,f110,f138,f804,f855,f963,f984,f1007])).
% 1.41/0.58  fof(f1007,plain,(
% 1.41/0.58    ~spl5_1 | spl5_5),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f999])).
% 1.41/0.58  fof(f999,plain,(
% 1.41/0.58    $false | (~spl5_1 | spl5_5)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f108,f56,f61,f26])).
% 1.41/0.58  fof(f26,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f16])).
% 1.41/0.58  fof(f16,plain,(
% 1.41/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.58    inference(ennf_transformation,[],[f1])).
% 1.41/0.58  fof(f1,axiom,(
% 1.41/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.58  fof(f61,plain,(
% 1.41/0.58    r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) | ~spl5_1),
% 1.41/0.58    inference(avatar_component_clause,[],[f59])).
% 1.41/0.58  fof(f59,plain,(
% 1.41/0.58    spl5_1 <=> r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.41/0.58  fof(f56,plain,(
% 1.41/0.58    ( ! [X4,X2,X1] : (r2_hidden(X4,k1_enumset1(X4,X1,X2))) )),
% 1.41/0.58    inference(equality_resolution,[],[f55])).
% 1.41/0.58  fof(f55,plain,(
% 1.41/0.58    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X4,X1,X2) != X3) )),
% 1.41/0.58    inference(equality_resolution,[],[f41])).
% 1.41/0.58  fof(f41,plain,(
% 1.41/0.58    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.41/0.58    inference(cnf_transformation,[],[f20])).
% 1.41/0.58  fof(f20,plain,(
% 1.41/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.41/0.58    inference(ennf_transformation,[],[f8])).
% 1.41/0.58  fof(f8,axiom,(
% 1.41/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.41/0.58  fof(f108,plain,(
% 1.41/0.58    ~r2_hidden(sK0,sK2) | spl5_5),
% 1.41/0.58    inference(avatar_component_clause,[],[f107])).
% 1.41/0.58  fof(f107,plain,(
% 1.41/0.58    spl5_5 <=> r2_hidden(sK0,sK2)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.41/0.58  fof(f984,plain,(
% 1.41/0.58    spl5_1 | ~spl5_2 | ~spl5_8),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f979])).
% 1.41/0.58  fof(f979,plain,(
% 1.41/0.58    $false | (spl5_1 | ~spl5_2 | ~spl5_8)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f858,f964,f25])).
% 1.41/0.58  fof(f25,plain,(
% 1.41/0.58    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f10])).
% 1.41/0.58  fof(f10,axiom,(
% 1.41/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.41/0.58  fof(f964,plain,(
% 1.41/0.58    ~r2_hidden(sK1,sK2) | (spl5_1 | ~spl5_8)),
% 1.41/0.58    inference(backward_demodulation,[],[f877,f799])).
% 1.41/0.58  fof(f799,plain,(
% 1.41/0.58    sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | ~spl5_8),
% 1.41/0.58    inference(avatar_component_clause,[],[f797])).
% 1.41/0.58  fof(f797,plain,(
% 1.41/0.58    spl5_8 <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.41/0.58  fof(f877,plain,(
% 1.41/0.58    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),sK2) | spl5_1),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f60,f28])).
% 1.41/0.58  fof(f28,plain,(
% 1.41/0.58    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f16])).
% 1.41/0.58  fof(f60,plain,(
% 1.41/0.58    ~r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) | spl5_1),
% 1.41/0.58    inference(avatar_component_clause,[],[f59])).
% 1.41/0.58  fof(f858,plain,(
% 1.41/0.58    r1_tarski(k1_tarski(sK1),sK2) | ~spl5_2),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f65,f24])).
% 1.41/0.58  fof(f24,plain,(
% 1.41/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f10])).
% 1.41/0.58  fof(f65,plain,(
% 1.41/0.58    r2_hidden(sK1,sK2) | ~spl5_2),
% 1.41/0.58    inference(avatar_component_clause,[],[f63])).
% 1.41/0.58  fof(f63,plain,(
% 1.41/0.58    spl5_2 <=> r2_hidden(sK1,sK2)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.41/0.58  fof(f963,plain,(
% 1.41/0.58    spl5_1 | ~spl5_5 | ~spl5_9),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f948])).
% 1.41/0.58  fof(f948,plain,(
% 1.41/0.58    $false | (spl5_1 | ~spl5_5 | ~spl5_9)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f113,f880,f25])).
% 1.41/0.58  fof(f880,plain,(
% 1.41/0.58    ~r2_hidden(sK0,sK2) | (spl5_1 | ~spl5_9)),
% 1.41/0.58    inference(forward_demodulation,[],[f877,f803])).
% 1.41/0.58  fof(f803,plain,(
% 1.41/0.58    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | ~spl5_9),
% 1.41/0.58    inference(avatar_component_clause,[],[f801])).
% 1.41/0.58  fof(f801,plain,(
% 1.41/0.58    spl5_9 <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.41/0.58  fof(f113,plain,(
% 1.41/0.58    r1_tarski(k1_tarski(sK0),sK2) | ~spl5_5),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f109,f24])).
% 1.41/0.58  fof(f109,plain,(
% 1.41/0.58    r2_hidden(sK0,sK2) | ~spl5_5),
% 1.41/0.58    inference(avatar_component_clause,[],[f107])).
% 1.41/0.58  fof(f855,plain,(
% 1.41/0.58    ~spl5_1 | spl5_2),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f845])).
% 1.41/0.58  fof(f845,plain,(
% 1.41/0.58    $false | (~spl5_1 | spl5_2)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f64,f52,f61,f26])).
% 1.41/0.58  fof(f52,plain,(
% 1.41/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_enumset1(X0,X1,X4))) )),
% 1.41/0.58    inference(equality_resolution,[],[f51])).
% 1.41/0.58  fof(f51,plain,(
% 1.41/0.58    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X0,X1,X4) != X3) )),
% 1.41/0.58    inference(equality_resolution,[],[f43])).
% 1.41/0.58  fof(f43,plain,(
% 1.41/0.58    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.41/0.58    inference(cnf_transformation,[],[f20])).
% 1.41/0.58  fof(f64,plain,(
% 1.41/0.58    ~r2_hidden(sK1,sK2) | spl5_2),
% 1.41/0.58    inference(avatar_component_clause,[],[f63])).
% 1.41/0.58  fof(f804,plain,(
% 1.41/0.58    spl5_8 | spl5_9 | spl5_1),
% 1.41/0.58    inference(avatar_split_clause,[],[f291,f59,f801,f797])).
% 1.41/0.58  fof(f291,plain,(
% 1.41/0.58    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | spl5_1),
% 1.41/0.58    inference(duplicate_literal_removal,[],[f288])).
% 1.41/0.58  fof(f288,plain,(
% 1.41/0.58    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2) | spl5_1),
% 1.41/0.58    inference(resolution,[],[f145,f57])).
% 1.41/0.58  fof(f57,plain,(
% 1.41/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.41/0.58    inference(equality_resolution,[],[f40])).
% 1.41/0.58  fof(f40,plain,(
% 1.41/0.58    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.41/0.58    inference(cnf_transformation,[],[f20])).
% 1.41/0.58  fof(f145,plain,(
% 1.41/0.58    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1)) | spl5_1),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f60,f27])).
% 1.41/0.58  fof(f27,plain,(
% 1.41/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f16])).
% 1.41/0.58  fof(f138,plain,(
% 1.41/0.58    ~spl5_1 | ~spl5_2 | ~spl5_5),
% 1.41/0.58    inference(avatar_split_clause,[],[f46,f107,f63,f59])).
% 1.41/0.58  fof(f46,plain,(
% 1.41/0.58    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | ~r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 1.41/0.58    inference(definition_unfolding,[],[f21,f34])).
% 1.41/0.58  fof(f34,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f9])).
% 1.41/0.58  fof(f9,axiom,(
% 1.41/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.58  fof(f21,plain,(
% 1.41/0.58    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.41/0.58    inference(cnf_transformation,[],[f15])).
% 1.41/0.58  fof(f15,plain,(
% 1.41/0.58    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.41/0.58    inference(ennf_transformation,[],[f14])).
% 1.41/0.58  fof(f14,negated_conjecture,(
% 1.41/0.58    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.41/0.58    inference(negated_conjecture,[],[f13])).
% 1.41/0.58  fof(f13,conjecture,(
% 1.41/0.58    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.41/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.41/0.58  fof(f110,plain,(
% 1.41/0.58    spl5_1 | spl5_5),
% 1.41/0.58    inference(avatar_split_clause,[],[f45,f107,f59])).
% 1.41/0.58  fof(f45,plain,(
% 1.41/0.58    r2_hidden(sK0,sK2) | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 1.41/0.58    inference(definition_unfolding,[],[f22,f34])).
% 1.41/0.58  fof(f22,plain,(
% 1.41/0.58    r2_hidden(sK0,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.41/0.58    inference(cnf_transformation,[],[f15])).
% 1.41/0.58  fof(f66,plain,(
% 1.41/0.58    spl5_1 | spl5_2),
% 1.41/0.58    inference(avatar_split_clause,[],[f44,f63,f59])).
% 1.41/0.58  fof(f44,plain,(
% 1.41/0.58    r2_hidden(sK1,sK2) | r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)),
% 1.41/0.58    inference(definition_unfolding,[],[f23,f34])).
% 1.41/0.58  fof(f23,plain,(
% 1.41/0.58    r2_hidden(sK1,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.41/0.58    inference(cnf_transformation,[],[f15])).
% 1.41/0.58  % SZS output end Proof for theBenchmark
% 1.41/0.58  % (26157)------------------------------
% 1.41/0.58  % (26157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (26157)Termination reason: Refutation
% 1.41/0.58  
% 1.41/0.58  % (26157)Memory used [KB]: 6652
% 1.41/0.58  % (26157)Time elapsed: 0.171 s
% 1.41/0.58  % (26157)------------------------------
% 1.41/0.58  % (26157)------------------------------
% 1.41/0.58  % (26150)Success in time 0.216 s
%------------------------------------------------------------------------------
