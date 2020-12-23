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
% DateTime   : Thu Dec  3 12:30:41 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    0
%              Number of atoms          :   78 (  78 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (4526)Refutation not found, incomplete strategy% (4526)------------------------------
% (4526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4526)Termination reason: Refutation not found, incomplete strategy

% (4526)Memory used [KB]: 10618
% (4526)Time elapsed: 0.151 s
% (4526)------------------------------
% (4526)------------------------------
tff(u296,axiom,(
    ! [X1,X0] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) )).

tff(u295,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u294,negated_conjecture,
    ( ~ ! [X1] : r1_xboole_0(sK1,X1)
    | ! [X5] : k1_xboole_0 = k3_xboole_0(X5,sK1) )).

tff(u293,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

tff(u292,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) )).

tff(u291,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK0)
    | k1_xboole_0 = k3_xboole_0(sK1,sK0) )).

tff(u290,negated_conjecture,
    ( ~ ! [X1] : r1_xboole_0(sK1,X1)
    | ! [X5] : k1_xboole_0 = k3_xboole_0(sK1,X5) )).

tff(u289,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) )).

tff(u288,negated_conjecture,
    ( ~ r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) )).

tff(u287,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u286,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u285,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ! [X0] : ~ r2_hidden(X0,k1_xboole_0) )).

tff(u284,negated_conjecture,
    ( ~ r1_tarski(sK1,sK0)
    | ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) ) )).

tff(u283,axiom,(
    ! [X3,X5,X4] :
      ( ~ r2_hidden(sK3(X3,X4),X5)
      | ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X3,X4) ) )).

tff(u282,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK3(X0,X1),X2)
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) )).

tff(u281,negated_conjecture,
    ( ~ ! [X1] : r1_xboole_0(sK1,X1)
    | ! [X9,X8] :
        ( ~ r2_hidden(sK2(X8,X9),sK1)
        | r1_xboole_0(X8,X9) ) )).

tff(u280,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) )).

tff(u279,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) )).

tff(u278,negated_conjecture,
    ( ~ r1_tarski(sK1,sK0)
    | ! [X0] :
        ( r2_hidden(sK3(sK1,X0),sK0)
        | r1_xboole_0(sK1,X0) ) )).

tff(u277,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) )).

tff(u276,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) )).

tff(u275,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) )).

tff(u274,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k3_xboole_0(X0,X1),X2) ) )).

tff(u273,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u272,axiom,(
    ! [X3,X2] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X3,X2) ) )).

tff(u271,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) )).

tff(u270,axiom,(
    ! [X3,X2,X4] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X3),X4)
      | ~ r2_hidden(sK2(X2,X3),X4)
      | r1_xboole_0(X2,X3) ) )).

tff(u269,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ! [X1] : r1_xboole_0(X1,k1_xboole_0) )).

tff(u268,negated_conjecture,
    ( ~ ! [X1] : r1_xboole_0(sK1,X1)
    | ! [X0] : r1_xboole_0(X0,sK1) )).

tff(u267,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ! [X0] : r1_xboole_0(k1_xboole_0,X0) )).

tff(u266,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) )).

tff(u265,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK0)
    | r1_xboole_0(sK1,sK0) )).

tff(u264,negated_conjecture,
    ( ~ ! [X1] : r1_xboole_0(sK1,X1)
    | ! [X1] : r1_xboole_0(sK1,X1) )).

tff(u263,negated_conjecture,
    ( ~ ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK1) )).

tff(u262,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.51  % (4511)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (4516)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (4514)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (4508)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (4523)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (4510)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (4509)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (4510)Refutation not found, incomplete strategy% (4510)------------------------------
% 0.22/0.52  % (4510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4510)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4510)Memory used [KB]: 10618
% 0.22/0.52  % (4510)Time elapsed: 0.106 s
% 0.22/0.52  % (4510)------------------------------
% 0.22/0.52  % (4510)------------------------------
% 0.22/0.53  % (4533)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (4528)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (4528)Refutation not found, incomplete strategy% (4528)------------------------------
% 0.22/0.53  % (4528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4528)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (4528)Memory used [KB]: 1663
% 0.22/0.53  % (4528)Time elapsed: 0.085 s
% 0.22/0.53  % (4528)------------------------------
% 0.22/0.53  % (4528)------------------------------
% 0.22/0.53  % (4533)Refutation not found, incomplete strategy% (4533)------------------------------
% 0.22/0.53  % (4533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4525)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (4533)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (4533)Memory used [KB]: 10618
% 0.22/0.53  % (4533)Time elapsed: 0.111 s
% 0.22/0.53  % (4533)------------------------------
% 0.22/0.53  % (4533)------------------------------
% 0.22/0.53  % (4507)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (4512)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (4520)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (4532)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (4513)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (4524)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (4535)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (4530)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (4536)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (4534)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (4522)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (4529)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (4526)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (4518)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (4527)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (4521)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (4519)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (4515)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (4517)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (4516)Refutation not found, incomplete strategy% (4516)------------------------------
% 0.22/0.55  % (4516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4516)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4516)Memory used [KB]: 10618
% 0.22/0.55  % (4516)Time elapsed: 0.138 s
% 0.22/0.55  % (4516)------------------------------
% 0.22/0.55  % (4516)------------------------------
% 0.22/0.55  % (4515)Refutation not found, incomplete strategy% (4515)------------------------------
% 0.22/0.55  % (4515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4524)Refutation not found, incomplete strategy% (4524)------------------------------
% 0.22/0.55  % (4524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4523)# SZS output start Saturation.
% 0.22/0.55  % (4526)Refutation not found, incomplete strategy% (4526)------------------------------
% 0.22/0.55  % (4526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4526)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4526)Memory used [KB]: 10618
% 0.22/0.55  % (4526)Time elapsed: 0.151 s
% 0.22/0.55  % (4526)------------------------------
% 0.22/0.55  % (4526)------------------------------
% 0.22/0.55  tff(u296,axiom,
% 0.22/0.55      (![X1, X0] : (((k3_xboole_0(X0,X1) != k1_xboole_0) | r1_xboole_0(X0,X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u295,negated_conjecture,
% 0.22/0.55      ((~(![X0] : (~r2_hidden(X0,k1_xboole_0)))) | (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u294,negated_conjecture,
% 0.22/0.55      ((~(![X1] : (r1_xboole_0(sK1,X1)))) | (![X5] : ((k1_xboole_0 = k3_xboole_0(X5,sK1)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u293,negated_conjecture,
% 0.22/0.55      ((~(![X0] : (~r2_hidden(X0,k1_xboole_0)))) | (![X0] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u292,negated_conjecture,
% 0.22/0.55      ((~(k1_xboole_0 = k3_xboole_0(sK0,sK1))) | (k1_xboole_0 = k3_xboole_0(sK0,sK1)))).
% 0.22/0.55  
% 0.22/0.55  tff(u291,negated_conjecture,
% 0.22/0.55      ((~(k1_xboole_0 = k3_xboole_0(sK1,sK0))) | (k1_xboole_0 = k3_xboole_0(sK1,sK0)))).
% 0.22/0.55  
% 0.22/0.55  tff(u290,negated_conjecture,
% 0.22/0.55      ((~(![X1] : (r1_xboole_0(sK1,X1)))) | (![X5] : ((k1_xboole_0 = k3_xboole_0(sK1,X5)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u289,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u288,negated_conjecture,
% 0.22/0.55      ((~r1_tarski(sK1,sK0)) | r1_tarski(sK1,sK0))).
% 0.22/0.55  
% 0.22/0.55  tff(u287,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u286,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u285,negated_conjecture,
% 0.22/0.55      ((~(![X0] : (~r2_hidden(X0,k1_xboole_0)))) | (![X0] : (~r2_hidden(X0,k1_xboole_0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u284,negated_conjecture,
% 0.22/0.55      ((~r1_tarski(sK1,sK0)) | (![X0] : ((~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u283,axiom,
% 0.22/0.55      (![X3, X5, X4] : ((~r2_hidden(sK3(X3,X4),X5) | ~r1_xboole_0(X4,X5) | r1_xboole_0(X3,X4))))).
% 0.22/0.55  
% 0.22/0.55  tff(u282,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~r2_hidden(sK3(X0,X1),X2) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u281,negated_conjecture,
% 0.22/0.55      ((~(![X1] : (r1_xboole_0(sK1,X1)))) | (![X9, X8] : ((~r2_hidden(sK2(X8,X9),sK1) | r1_xboole_0(X8,X9)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u280,axiom,
% 0.22/0.55      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u279,axiom,
% 0.22/0.55      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u278,negated_conjecture,
% 0.22/0.55      ((~r1_tarski(sK1,sK0)) | (![X0] : ((r2_hidden(sK3(sK1,X0),sK0) | r1_xboole_0(sK1,X0)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u277,axiom,
% 0.22/0.55      (![X1, X0] : ((r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u276,axiom,
% 0.22/0.55      (![X1, X0] : ((~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u275,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~r1_xboole_0(X1,X2) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))))).
% 0.22/0.55  
% 0.22/0.55  tff(u274,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),X2))))).
% 0.22/0.55  
% 0.22/0.55  tff(u273,axiom,
% 0.22/0.55      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k3_xboole_0(X0,X1) = k1_xboole_0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u272,axiom,
% 0.22/0.55      (![X3, X2] : ((~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2))))).
% 0.22/0.55  
% 0.22/0.55  tff(u271,axiom,
% 0.22/0.55      (![X1, X0] : ((~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u270,axiom,
% 0.22/0.55      (![X3, X2, X4] : ((~r1_xboole_0(k3_xboole_0(X2,X3),X4) | ~r2_hidden(sK2(X2,X3),X4) | r1_xboole_0(X2,X3))))).
% 0.22/0.55  
% 0.22/0.55  tff(u269,negated_conjecture,
% 0.22/0.55      ((~(![X0] : (~r2_hidden(X0,k1_xboole_0)))) | (![X1] : (r1_xboole_0(X1,k1_xboole_0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u268,negated_conjecture,
% 0.22/0.55      ((~(![X1] : (r1_xboole_0(sK1,X1)))) | (![X0] : (r1_xboole_0(X0,sK1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u267,negated_conjecture,
% 0.22/0.55      ((~(![X0] : (~r2_hidden(X0,k1_xboole_0)))) | (![X0] : (r1_xboole_0(k1_xboole_0,X0))))).
% 0.22/0.55  
% 0.22/0.56  tff(u266,negated_conjecture,
% 0.22/0.56      ((~r1_xboole_0(sK0,sK1)) | r1_xboole_0(sK0,sK1))).
% 0.22/0.56  
% 0.22/0.56  tff(u265,negated_conjecture,
% 0.22/0.56      ((~r1_xboole_0(sK1,sK0)) | r1_xboole_0(sK1,sK0))).
% 0.22/0.56  
% 0.22/0.56  tff(u264,negated_conjecture,
% 0.22/0.56      ((~(![X1] : (r1_xboole_0(sK1,X1)))) | (![X1] : (r1_xboole_0(sK1,X1))))).
% 0.22/0.56  
% 0.22/0.56  tff(u263,negated_conjecture,
% 0.22/0.56      ((~~v1_xboole_0(sK1)) | ~v1_xboole_0(sK1))).
% 0.22/0.56  
% 0.22/0.56  tff(u262,axiom,
% 0.22/0.56      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.22/0.56  
% 0.22/0.56  % (4523)# SZS output end Saturation.
% 0.22/0.56  % (4523)------------------------------
% 0.22/0.56  % (4523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4523)Termination reason: Satisfiable
% 0.22/0.56  
% 0.22/0.56  % (4523)Memory used [KB]: 10746
% 0.22/0.56  % (4523)Time elapsed: 0.115 s
% 0.22/0.56  % (4523)------------------------------
% 0.22/0.56  % (4523)------------------------------
% 0.22/0.56  % (4506)Success in time 0.196 s
%------------------------------------------------------------------------------
