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
% DateTime   : Thu Dec  3 12:37:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 169 expanded)
%              Number of leaves         :   15 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  194 ( 392 expanded)
%              Number of equality atoms :   19 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f59,f1052,f1077,f1095,f1102,f1147,f1152])).

fof(f1152,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f1133])).

fof(f1133,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f56,f48,f183])).

fof(f183,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X5),X6),X7)
      | r2_hidden(X5,X7) ) ),
    inference(resolution,[],[f180,f20])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X2)
      | ~ r1_tarski(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f175])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(k1_tarski(X2),X0)
      | r2_hidden(X2,X1)
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f158,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f158,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(X8,k2_xboole_0(X11,X10))
      | ~ r1_tarski(X9,X10)
      | ~ r1_tarski(k1_tarski(X8),X9) ) ),
    inference(resolution,[],[f92,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f92,plain,(
    ! [X14,X12,X15,X13] :
      ( r1_tarski(X12,k2_xboole_0(X14,X15))
      | ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X13,X15) ) ),
    inference(resolution,[],[f30,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f48,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_1
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f56,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1147,plain,
    ( ~ spl4_1
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1128])).

fof(f1128,plain,
    ( $false
    | ~ spl4_1
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f728,f20,f48,f30])).

fof(f728,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f726])).

fof(f726,plain,
    ( spl4_7
  <=> r1_tarski(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1102,plain,
    ( ~ spl4_3
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1098])).

fof(f1098,plain,
    ( $false
    | ~ spl4_3
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f57,f40,f728,f93])).

fof(f93,plain,(
    ! [X17,X18,X16] :
      ( ~ r1_tarski(X16,k1_tarski(X17))
      | r1_tarski(X16,X18)
      | ~ r2_hidden(X17,X18) ) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

% (10718)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f57,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f1095,plain,
    ( ~ spl4_5
    | ~ spl4_7
    | spl4_1 ),
    inference(avatar_split_clause,[],[f1092,f46,f726,f636])).

fof(f636,plain,
    ( spl4_5
  <=> r1_tarski(k1_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1092,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK2)
    | ~ r1_tarski(k1_tarski(sK1),sK2)
    | spl4_1 ),
    inference(resolution,[],[f47,f576])).

fof(f576,plain,(
    ! [X68,X69,X67] :
      ( r1_tarski(k2_xboole_0(X69,X67),X68)
      | ~ r1_tarski(X69,X68)
      | ~ r1_tarski(X67,X68) ) ),
    inference(superposition,[],[f98,f508])).

fof(f508,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(X1,X2) = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f443,f84])).

fof(f84,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_xboole_0(X3,X4),X4)
      | k2_xboole_0(X3,X4) = X4 ) ),
    inference(resolution,[],[f25,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f443,plain,(
    ! [X8,X7] :
      ( r1_tarski(k2_xboole_0(X8,X7),X7)
      | ~ r1_tarski(X8,X7) ) ),
    inference(superposition,[],[f29,f426])).

fof(f426,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(subsumption_resolution,[],[f381,f424])).

fof(f424,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(X1,X1,X1),X1)
      | k2_xboole_0(X1,X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f420])).

fof(f420,plain,(
    ! [X1] :
      ( k2_xboole_0(X1,X1) = X1
      | ~ r2_hidden(sK3(X1,X1,X1),X1)
      | k2_xboole_0(X1,X1) = X1 ) ),
    inference(resolution,[],[f381,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f381,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,X0,X0),X0)
      | k2_xboole_0(X0,X0) = X0 ) ),
    inference(factoring,[],[f224])).

fof(f224,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | r2_hidden(sK3(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X2,X1),k2_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f29,f21])).

fof(f47,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f1077,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f1058])).

fof(f1058,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f51,f48,f184])).

fof(f184,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(k2_xboole_0(X8,k1_tarski(X9)),X10)
      | r2_hidden(X9,X10) ) ),
    inference(resolution,[],[f180,f60])).

fof(f51,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1052,plain,
    ( ~ spl4_2
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f1048])).

fof(f1048,plain,
    ( $false
    | ~ spl4_2
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f52,f40,f638,f93])).

fof(f638,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f636])).

fof(f52,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f59,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f39,f55,f50,f46])).

% (10723)Refutation not found, incomplete strategy% (10723)------------------------------
% (10723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10723)Termination reason: Refutation not found, incomplete strategy

% (10723)Memory used [KB]: 1663
% (10723)Time elapsed: 0.105 s
% (10723)------------------------------
% (10723)------------------------------
fof(f39,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f17,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f58,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f38,f55,f46])).

fof(f38,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f18,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f37,f50,f46])).

fof(f37,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f19,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (10707)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.48  % (10715)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (10702)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (10695)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (10716)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (10696)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (10708)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (10697)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (10698)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (10699)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (10700)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (10707)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (10713)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (10723)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (10721)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1153,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f53,f58,f59,f1052,f1077,f1095,f1102,f1147,f1152])).
% 0.21/0.54  fof(f1152,plain,(
% 0.21/0.54    ~spl4_1 | spl4_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1133])).
% 0.21/0.54  fof(f1133,plain,(
% 0.21/0.54    $false | (~spl4_1 | spl4_3)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f56,f48,f183])).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    ( ! [X6,X7,X5] : (~r1_tarski(k2_xboole_0(k1_tarski(X5),X6),X7) | r2_hidden(X5,X7)) )),
% 0.21/0.54    inference(resolution,[],[f180,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),X2) | ~r1_tarski(X2,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(condensation,[],[f175])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(k1_tarski(X2),X0) | r2_hidden(X2,X1) | r2_hidden(X2,X3)) )),
% 0.21/0.54    inference(resolution,[],[f158,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X10,X8,X11,X9] : (r2_hidden(X8,k2_xboole_0(X11,X10)) | ~r1_tarski(X9,X10) | ~r1_tarski(k1_tarski(X8),X9)) )),
% 0.21/0.54    inference(resolution,[],[f92,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X14,X12,X15,X13] : (r1_tarski(X12,k2_xboole_0(X14,X15)) | ~r1_tarski(X12,X13) | ~r1_tarski(X13,X15)) )),
% 0.21/0.54    inference(resolution,[],[f30,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | ~spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    spl4_1 <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK2) | spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    spl4_3 <=> r2_hidden(sK0,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f1147,plain,(
% 0.21/0.54    ~spl4_1 | spl4_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1128])).
% 0.21/0.54  fof(f1128,plain,(
% 0.21/0.54    $false | (~spl4_1 | spl4_7)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f728,f20,f48,f30])).
% 0.21/0.54  fof(f728,plain,(
% 0.21/0.54    ~r1_tarski(k1_tarski(sK0),sK2) | spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f726])).
% 0.21/0.54  fof(f726,plain,(
% 0.21/0.54    spl4_7 <=> r1_tarski(k1_tarski(sK0),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f1102,plain,(
% 0.21/0.54    ~spl4_3 | spl4_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1098])).
% 0.21/0.54  fof(f1098,plain,(
% 0.21/0.54    $false | (~spl4_3 | spl4_7)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f57,f40,f728,f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ( ! [X17,X18,X16] : (~r1_tarski(X16,k1_tarski(X17)) | r1_tarski(X16,X18) | ~r2_hidden(X17,X18)) )),
% 0.21/0.54    inference(resolution,[],[f30,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  % (10718)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    r2_hidden(sK0,sK2) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f55])).
% 0.21/0.54  fof(f1095,plain,(
% 0.21/0.54    ~spl4_5 | ~spl4_7 | spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f1092,f46,f726,f636])).
% 0.21/0.54  fof(f636,plain,(
% 0.21/0.54    spl4_5 <=> r1_tarski(k1_tarski(sK1),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f1092,plain,(
% 0.21/0.54    ~r1_tarski(k1_tarski(sK0),sK2) | ~r1_tarski(k1_tarski(sK1),sK2) | spl4_1),
% 0.21/0.54    inference(resolution,[],[f47,f576])).
% 0.21/0.54  fof(f576,plain,(
% 0.21/0.54    ( ! [X68,X69,X67] : (r1_tarski(k2_xboole_0(X69,X67),X68) | ~r1_tarski(X69,X68) | ~r1_tarski(X67,X68)) )),
% 0.21/0.54    inference(superposition,[],[f98,f508])).
% 0.21/0.54  fof(f508,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = X2 | ~r1_tarski(X1,X2)) )),
% 0.21/0.54    inference(resolution,[],[f443,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~r1_tarski(k2_xboole_0(X3,X4),X4) | k2_xboole_0(X3,X4) = X4) )),
% 0.21/0.54    inference(resolution,[],[f25,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.54    inference(superposition,[],[f20,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f443,plain,(
% 0.21/0.54    ( ! [X8,X7] : (r1_tarski(k2_xboole_0(X8,X7),X7) | ~r1_tarski(X8,X7)) )),
% 0.21/0.54    inference(superposition,[],[f29,f426])).
% 0.21/0.54  fof(f426,plain,(
% 0.21/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f381,f424])).
% 0.21/0.54  fof(f424,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK3(X1,X1,X1),X1) | k2_xboole_0(X1,X1) = X1) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f420])).
% 0.21/0.54  fof(f420,plain,(
% 0.21/0.54    ( ! [X1] : (k2_xboole_0(X1,X1) = X1 | ~r2_hidden(sK3(X1,X1,X1),X1) | k2_xboole_0(X1,X1) = X1) )),
% 0.21/0.54    inference(resolution,[],[f381,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(X0,X0,X0),X0) | k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.54    inference(factoring,[],[f224])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | r2_hidden(sK3(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.54    inference(factoring,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X2,X1),k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X0)) )),
% 0.21/0.54    inference(superposition,[],[f29,f21])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ~r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f46])).
% 0.21/0.54  fof(f1077,plain,(
% 0.21/0.54    ~spl4_1 | spl4_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1058])).
% 0.21/0.54  fof(f1058,plain,(
% 0.21/0.54    $false | (~spl4_1 | spl4_2)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f51,f48,f184])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    ( ! [X10,X8,X9] : (~r1_tarski(k2_xboole_0(X8,k1_tarski(X9)),X10) | r2_hidden(X9,X10)) )),
% 0.21/0.54    inference(resolution,[],[f180,f60])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK2) | spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    spl4_2 <=> r2_hidden(sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f1052,plain,(
% 0.21/0.54    ~spl4_2 | spl4_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1048])).
% 0.21/0.54  fof(f1048,plain,(
% 0.21/0.54    $false | (~spl4_2 | spl4_5)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f52,f40,f638,f93])).
% 0.21/0.54  fof(f638,plain,(
% 0.21/0.54    ~r1_tarski(k1_tarski(sK1),sK2) | spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f636])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    r2_hidden(sK1,sK2) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f50])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f55,f50,f46])).
% 0.21/0.54  % (10723)Refutation not found, incomplete strategy% (10723)------------------------------
% 0.21/0.54  % (10723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10723)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10723)Memory used [KB]: 1663
% 0.21/0.54  % (10723)Time elapsed: 0.105 s
% 0.21/0.54  % (10723)------------------------------
% 0.21/0.54  % (10723)------------------------------
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | ~r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 0.21/0.54    inference(definition_unfolding,[],[f17,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    spl4_1 | spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f55,f46])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    r2_hidden(sK0,sK2) | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 0.21/0.54    inference(definition_unfolding,[],[f18,f22])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    r2_hidden(sK0,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    spl4_1 | spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f37,f50,f46])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    r2_hidden(sK1,sK2) | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 0.21/0.54    inference(definition_unfolding,[],[f19,f22])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    r2_hidden(sK1,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (10707)------------------------------
% 0.21/0.54  % (10707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10707)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (10707)Memory used [KB]: 6908
% 0.21/0.54  % (10707)Time elapsed: 0.123 s
% 0.21/0.54  % (10707)------------------------------
% 0.21/0.54  % (10707)------------------------------
% 0.21/0.54  % (10693)Success in time 0.182 s
%------------------------------------------------------------------------------
