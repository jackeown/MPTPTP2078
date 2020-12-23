%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 167 expanded)
%              Number of leaves         :   10 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  103 ( 333 expanded)
%              Number of equality atoms :   19 (  76 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f663,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f642,f643])).

fof(f643,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f617])).

fof(f617,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f571,f61])).

fof(f61,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_1
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f571,plain,(
    ! [X26,X27] : r1_tarski(k3_xboole_0(X27,X26),X26) ),
    inference(superposition,[],[f39,f539])).

fof(f539,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X3,X2)) = X2 ),
    inference(superposition,[],[f471,f104])).

fof(f104,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k3_xboole_0(X13,X12)) = k3_xboole_0(k2_xboole_0(X12,X13),X12) ),
    inference(resolution,[],[f23,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f39,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f21,f19])).

fof(f19,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).

fof(f471,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f395,f20])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f395,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k3_xboole_0(X3,X2) = X2 ) ),
    inference(subsumption_resolution,[],[f392,f41])).

fof(f392,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X2)
      | ~ r1_tarski(X2,X3)
      | k3_xboole_0(X3,X2) = X2 ) ),
    inference(duplicate_literal_removal,[],[f390])).

fof(f390,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X2)
      | ~ r1_tarski(X2,X3)
      | k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X2)
      | ~ r1_tarski(X2,X3)
      | k3_xboole_0(X3,X2) = X2 ) ),
    inference(resolution,[],[f26,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X2),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK3(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(subsumption_resolution,[],[f35,f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X0))
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f22,f28])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f642,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f618])).

fof(f618,plain,
    ( $false
    | spl4_2 ),
    inference(resolution,[],[f571,f65])).

fof(f65,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_2
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f66,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f49,f63,f59])).

fof(f49,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f27,f18])).

fof(f18,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:49:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (27139)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.41  % (27138)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (27141)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (27135)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.45  % (27136)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.45  % (27145)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.45  % (27137)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.45  % (27134)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.46  % (27133)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.46  % (27143)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.47  % (27144)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.47  % (27142)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.49  % (27133)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f663,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f66,f642,f643])).
% 0.20/0.49  fof(f643,plain,(
% 0.20/0.49    spl4_1),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f617])).
% 0.20/0.49  fof(f617,plain,(
% 0.20/0.49    $false | spl4_1),
% 0.20/0.49    inference(resolution,[],[f571,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    spl4_1 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f571,plain,(
% 0.20/0.49    ( ! [X26,X27] : (r1_tarski(k3_xboole_0(X27,X26),X26)) )),
% 0.20/0.49    inference(superposition,[],[f39,f539])).
% 0.20/0.49  fof(f539,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X3,X2)) = X2) )),
% 0.20/0.49    inference(superposition,[],[f471,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X12,X13] : (k2_xboole_0(X12,k3_xboole_0(X13,X12)) = k3_xboole_0(k2_xboole_0(X12,X13),X12)) )),
% 0.20/0.49    inference(resolution,[],[f23,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.49    inference(superposition,[],[f39,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.49    inference(resolution,[],[f21,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).
% 0.20/0.50  fof(f471,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0) )),
% 0.20/0.50    inference(resolution,[],[f395,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.50  fof(f395,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k3_xboole_0(X3,X2) = X2) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f392,f41])).
% 0.20/0.50  fof(f392,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r1_tarski(X2,X2) | ~r1_tarski(X2,X3) | k3_xboole_0(X3,X2) = X2) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f390])).
% 0.20/0.50  fof(f390,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r1_tarski(X2,X2) | ~r1_tarski(X2,X3) | k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X2) | ~r1_tarski(X2,X3) | k3_xboole_0(X3,X2) = X2) )),
% 0.20/0.50    inference(resolution,[],[f26,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(sK3(X0,X1,X2),X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k3_xboole_0(X1,X2) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(sK3(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k3_xboole_0(X1,X2) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f35,f19])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0)) | ~r1_tarski(k1_xboole_0,X1)) )),
% 0.20/0.50    inference(superposition,[],[f22,f28])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
% 0.20/0.50  fof(f642,plain,(
% 0.20/0.50    spl4_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f618])).
% 0.20/0.50  fof(f618,plain,(
% 0.20/0.50    $false | spl4_2),
% 0.20/0.50    inference(resolution,[],[f571,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ~r1_tarski(k3_xboole_0(sK0,sK2),sK2) | spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    spl4_2 <=> r1_tarski(k3_xboole_0(sK0,sK2),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ~spl4_1 | ~spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f49,f63,f59])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ~r1_tarski(k3_xboole_0(sK0,sK2),sK2) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK1)),
% 0.20/0.50    inference(resolution,[],[f27,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ~r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.50    inference(negated_conjecture,[],[f8])).
% 0.20/0.50  fof(f8,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (27133)------------------------------
% 0.20/0.50  % (27133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27133)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (27133)Memory used [KB]: 11001
% 0.20/0.50  % (27133)Time elapsed: 0.095 s
% 0.20/0.50  % (27133)------------------------------
% 0.20/0.50  % (27133)------------------------------
% 0.20/0.50  % (27126)Success in time 0.147 s
%------------------------------------------------------------------------------
