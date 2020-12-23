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
% DateTime   : Thu Dec  3 12:30:33 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u114,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) )).

tff(u113,negated_conjecture,
    ( ~ ( k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0) )
    | k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0) )).

tff(u112,negated_conjecture,
    ( ~ ( k1_xboole_0 != sK0 )
    | k1_xboole_0 != sK0 )).

tff(u111,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

tff(u110,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))
    | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) )).

tff(u109,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) )).

tff(u108,negated_conjecture,
    ( ~ ~ r1_xboole_0(sK0,k4_xboole_0(sK0,sK0))
    | ~ r1_xboole_0(sK0,k4_xboole_0(sK0,sK0)) )).

tff(u107,axiom,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) )).

tff(u106,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK0)
    | r1_xboole_0(sK0,sK0) )).

tff(u105,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u104,axiom,
    ( ~ ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ! [X1] : ~ r2_hidden(X1,k1_xboole_0) )).

tff(u103,axiom,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) )).

tff(u102,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK2(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) )).

tff(u101,negated_conjecture,
    ( ~ r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK0)),k4_xboole_0(sK0,k1_xboole_0))
    | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK0)),k4_xboole_0(sK0,k1_xboole_0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (22884)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (22875)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (22884)Refutation not found, incomplete strategy% (22884)------------------------------
% 0.21/0.52  % (22884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22867)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (22884)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22884)Memory used [KB]: 10618
% 0.21/0.52  % (22884)Time elapsed: 0.066 s
% 0.21/0.52  % (22884)------------------------------
% 0.21/0.52  % (22884)------------------------------
% 0.21/0.53  % (22872)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (22867)Refutation not found, incomplete strategy% (22867)------------------------------
% 0.21/0.53  % (22867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22867)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22867)Memory used [KB]: 6268
% 0.21/0.53  % (22872)Refutation not found, incomplete strategy% (22872)------------------------------
% 0.21/0.53  % (22872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22872)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22872)Memory used [KB]: 10618
% 0.21/0.53  % (22872)Time elapsed: 0.105 s
% 0.21/0.53  % (22872)------------------------------
% 0.21/0.53  % (22872)------------------------------
% 0.21/0.53  % (22867)Time elapsed: 0.069 s
% 0.21/0.53  % (22867)------------------------------
% 0.21/0.53  % (22867)------------------------------
% 0.21/0.53  % (22889)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (22865)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (22880)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (22860)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (22860)Refutation not found, incomplete strategy% (22860)------------------------------
% 0.21/0.53  % (22860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22860)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22860)Memory used [KB]: 1663
% 0.21/0.53  % (22860)Time elapsed: 0.123 s
% 0.21/0.53  % (22860)------------------------------
% 0.21/0.53  % (22860)------------------------------
% 0.21/0.54  % (22865)Refutation not found, incomplete strategy% (22865)------------------------------
% 0.21/0.54  % (22865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22865)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22865)Memory used [KB]: 10746
% 0.21/0.54  % (22865)Time elapsed: 0.127 s
% 0.21/0.54  % (22865)------------------------------
% 0.21/0.54  % (22865)------------------------------
% 0.21/0.54  % (22866)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (22863)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (22866)Refutation not found, incomplete strategy% (22866)------------------------------
% 0.21/0.54  % (22866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22866)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22866)Memory used [KB]: 6140
% 0.21/0.54  % (22866)Time elapsed: 0.123 s
% 0.21/0.54  % (22866)------------------------------
% 0.21/0.54  % (22866)------------------------------
% 0.21/0.54  % (22863)Refutation not found, incomplete strategy% (22863)------------------------------
% 0.21/0.54  % (22863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22863)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22863)Memory used [KB]: 10618
% 0.21/0.54  % (22863)Time elapsed: 0.124 s
% 0.21/0.54  % (22863)------------------------------
% 0.21/0.54  % (22863)------------------------------
% 0.21/0.54  % (22888)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (22889)Refutation not found, incomplete strategy% (22889)------------------------------
% 0.21/0.54  % (22889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22877)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (22879)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (22885)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (22887)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (22871)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (22887)Refutation not found, incomplete strategy% (22887)------------------------------
% 0.21/0.54  % (22887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22887)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22887)Memory used [KB]: 6268
% 0.21/0.54  % (22887)Time elapsed: 0.138 s
% 0.21/0.54  % (22887)------------------------------
% 0.21/0.54  % (22887)------------------------------
% 0.21/0.54  % (22871)Refutation not found, incomplete strategy% (22871)------------------------------
% 0.21/0.54  % (22871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22871)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22871)Memory used [KB]: 10618
% 0.21/0.54  % (22871)Time elapsed: 0.140 s
% 0.21/0.54  % (22871)------------------------------
% 0.21/0.54  % (22871)------------------------------
% 0.21/0.54  % (22881)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (22886)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (22879)Refutation not found, incomplete strategy% (22879)------------------------------
% 0.21/0.55  % (22879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22879)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22879)Memory used [KB]: 10618
% 0.21/0.55  % (22879)Time elapsed: 0.140 s
% 0.21/0.55  % (22879)------------------------------
% 0.21/0.55  % (22879)------------------------------
% 0.21/0.55  % (22881)Refutation not found, incomplete strategy% (22881)------------------------------
% 0.21/0.55  % (22881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22881)Memory used [KB]: 10746
% 0.21/0.55  % (22881)Time elapsed: 0.138 s
% 0.21/0.55  % (22881)------------------------------
% 0.21/0.55  % (22881)------------------------------
% 0.21/0.55  % (22862)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (22874)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (22878)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (22888)Refutation not found, incomplete strategy% (22888)------------------------------
% 0.21/0.55  % (22888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22888)Memory used [KB]: 10746
% 0.21/0.55  % (22888)Time elapsed: 0.141 s
% 0.21/0.55  % (22888)------------------------------
% 0.21/0.55  % (22888)------------------------------
% 0.21/0.55  % (22876)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (22874)Refutation not found, incomplete strategy% (22874)------------------------------
% 0.21/0.55  % (22874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22874)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22874)Memory used [KB]: 6140
% 0.21/0.55  % (22874)Time elapsed: 0.134 s
% 0.21/0.55  % (22874)------------------------------
% 0.21/0.55  % (22874)------------------------------
% 0.21/0.55  % (22882)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (22890)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (22885)Refutation not found, incomplete strategy% (22885)------------------------------
% 0.21/0.55  % (22885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22873)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (22868)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (22885)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22885)Memory used [KB]: 1663
% 0.21/0.55  % (22885)Time elapsed: 0.149 s
% 0.21/0.55  % (22885)------------------------------
% 0.21/0.55  % (22885)------------------------------
% 0.21/0.55  % (22889)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22889)Memory used [KB]: 6268
% 0.21/0.55  % (22889)Time elapsed: 0.122 s
% 0.21/0.55  % (22889)------------------------------
% 0.21/0.55  % (22889)------------------------------
% 0.21/0.55  % (22883)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (22870)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (22883)Refutation not found, incomplete strategy% (22883)------------------------------
% 0.21/0.56  % (22883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22883)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22883)Memory used [KB]: 1663
% 0.21/0.56  % (22883)Time elapsed: 0.149 s
% 0.21/0.56  % (22883)------------------------------
% 0.21/0.56  % (22883)------------------------------
% 0.21/0.56  % (22870)Refutation not found, incomplete strategy% (22870)------------------------------
% 0.21/0.56  % (22870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22870)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22870)Memory used [KB]: 10618
% 0.21/0.56  % (22870)Time elapsed: 0.148 s
% 0.21/0.56  % (22870)------------------------------
% 0.21/0.56  % (22870)------------------------------
% 0.21/0.56  % (22869)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (22873)Refutation not found, incomplete strategy% (22873)------------------------------
% 0.21/0.56  % (22873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22873)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22873)Memory used [KB]: 10618
% 0.21/0.56  % (22873)Time elapsed: 0.154 s
% 0.21/0.56  % (22873)------------------------------
% 0.21/0.56  % (22873)------------------------------
% 0.21/0.56  % (22891)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (22882)Refutation not found, incomplete strategy% (22882)------------------------------
% 0.21/0.56  % (22882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22882)Memory used [KB]: 10618
% 0.21/0.56  % (22882)Time elapsed: 0.155 s
% 0.21/0.56  % (22882)------------------------------
% 0.21/0.56  % (22882)------------------------------
% 0.21/0.56  % (22891)Refutation not found, incomplete strategy% (22891)------------------------------
% 0.21/0.56  % (22891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22891)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22891)Memory used [KB]: 1663
% 0.21/0.56  % (22891)Time elapsed: 0.156 s
% 0.21/0.56  % (22891)------------------------------
% 0.21/0.56  % (22891)------------------------------
% 0.21/0.56  % (22877)Refutation not found, incomplete strategy% (22877)------------------------------
% 0.21/0.56  % (22877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22877)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22877)Memory used [KB]: 6140
% 0.21/0.56  % (22877)Time elapsed: 0.157 s
% 0.21/0.56  % (22877)------------------------------
% 0.21/0.56  % (22877)------------------------------
% 0.21/0.56  % (22886)Refutation not found, incomplete strategy% (22886)------------------------------
% 0.21/0.56  % (22886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22886)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22886)Memory used [KB]: 6268
% 0.21/0.56  % (22886)Time elapsed: 0.139 s
% 0.21/0.56  % (22886)------------------------------
% 0.21/0.56  % (22886)------------------------------
% 0.21/0.57  % (22878)# SZS output start Saturation.
% 0.21/0.57  tff(u114,axiom,
% 0.21/0.57      (![X1, X0] : (((k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1))))).
% 0.21/0.57  
% 0.21/0.57  tff(u113,negated_conjecture,
% 0.21/0.57      ((~(k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0))) | (k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0)))).
% 0.21/0.57  
% 0.21/0.57  tff(u112,negated_conjecture,
% 0.21/0.57      ((~(k1_xboole_0 != sK0)) | (k1_xboole_0 != sK0))).
% 0.21/0.57  
% 0.21/0.57  tff(u111,axiom,
% 0.21/0.57      (![X0] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0))))).
% 0.21/0.57  
% 0.21/0.57  tff(u110,negated_conjecture,
% 0.21/0.57      ((~(k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)))) | (k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))))).
% 0.21/0.57  
% 0.21/0.57  tff(u109,axiom,
% 0.21/0.57      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))))))).
% 0.21/0.57  
% 0.21/0.57  tff(u108,negated_conjecture,
% 0.21/0.57      ((~~r1_xboole_0(sK0,k4_xboole_0(sK0,sK0))) | ~r1_xboole_0(sK0,k4_xboole_0(sK0,sK0)))).
% 0.21/0.57  
% 0.21/0.57  tff(u107,axiom,
% 0.21/0.57      (![X0] : (r1_xboole_0(k1_xboole_0,X0)))).
% 0.21/0.57  
% 0.21/0.57  tff(u106,negated_conjecture,
% 0.21/0.57      ((~r1_xboole_0(sK0,sK0)) | r1_xboole_0(sK0,sK0))).
% 0.21/0.57  
% 0.21/0.57  tff(u105,axiom,
% 0.21/0.57      (![X1, X0, X2] : ((~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1))))).
% 0.21/0.57  
% 0.21/0.57  tff(u104,axiom,
% 0.21/0.57      ((~(![X1] : (~r2_hidden(X1,k1_xboole_0)))) | (![X1] : (~r2_hidden(X1,k1_xboole_0))))).
% 0.21/0.57  
% 0.21/0.57  tff(u103,axiom,
% 0.21/0.57      (![X0] : ((r2_hidden(sK1(X0),X0) | (k1_xboole_0 = X0))))).
% 0.21/0.57  
% 0.21/0.57  tff(u102,axiom,
% 0.21/0.57      (![X1, X0] : ((r2_hidden(sK2(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1))))).
% 0.21/0.57  
% 0.21/0.57  tff(u101,negated_conjecture,
% 0.21/0.57      ((~r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK0)),k4_xboole_0(sK0,k1_xboole_0))) | r2_hidden(sK2(sK0,k4_xboole_0(sK0,sK0)),k4_xboole_0(sK0,k1_xboole_0)))).
% 0.21/0.57  
% 0.21/0.57  % (22878)# SZS output end Saturation.
% 0.21/0.57  % (22878)------------------------------
% 0.21/0.57  % (22878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (22878)Termination reason: Satisfiable
% 0.21/0.57  
% 0.21/0.57  % (22878)Memory used [KB]: 10746
% 0.21/0.57  % (22878)Time elapsed: 0.139 s
% 0.21/0.57  % (22878)------------------------------
% 0.21/0.57  % (22878)------------------------------
% 0.21/0.57  % (22856)Success in time 0.194 s
%------------------------------------------------------------------------------
