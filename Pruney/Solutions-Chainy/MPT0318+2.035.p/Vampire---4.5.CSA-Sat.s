%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:20 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u90,negated_conjecture,
    ( ~ ( o_0_0_xboole_0 != sK0 )
    | o_0_0_xboole_0 != sK0 )).

tff(u89,axiom,
    ( o_0_0_xboole_0 != k1_xboole_0
    | ! [X1,X0] :
        ( o_0_0_xboole_0 != k2_zfmisc_1(X0,X1)
        | o_0_0_xboole_0 = X1
        | o_0_0_xboole_0 = X0 ) )).

tff(u88,axiom,
    ( o_0_0_xboole_0 != k1_xboole_0
    | o_0_0_xboole_0 = k1_xboole_0 )).

tff(u87,axiom,
    ( o_0_0_xboole_0 != k1_xboole_0
    | ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) )).

tff(u86,axiom,
    ( o_0_0_xboole_0 != k1_xboole_0
    | ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) )).

tff(u85,negated_conjecture,
    ( o_0_0_xboole_0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | o_0_0_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) )).

tff(u84,axiom,
    ( o_0_0_xboole_0 != k1_xboole_0
    | ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 ) )).

tff(u83,axiom,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(o_0_0_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:15:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (22360)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (22335)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (22361)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (22337)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (22353)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (22335)Refutation not found, incomplete strategy% (22335)------------------------------
% 0.21/0.52  % (22335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22335)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22335)Memory used [KB]: 10618
% 0.21/0.52  % (22335)Time elapsed: 0.114 s
% 0.21/0.52  % (22335)------------------------------
% 0.21/0.52  % (22335)------------------------------
% 0.21/0.53  % (22355)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (22350)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (22355)Refutation not found, incomplete strategy% (22355)------------------------------
% 0.21/0.53  % (22355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22355)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22355)Memory used [KB]: 10618
% 0.21/0.53  % (22355)Time elapsed: 0.136 s
% 0.21/0.53  % (22355)------------------------------
% 0.21/0.53  % (22355)------------------------------
% 0.21/0.54  % (22363)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (22333)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (22358)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (22343)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (22336)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (22359)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (22337)Refutation not found, incomplete strategy% (22337)------------------------------
% 0.21/0.54  % (22337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22337)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22337)Memory used [KB]: 6140
% 0.21/0.54  % (22337)Time elapsed: 0.141 s
% 0.21/0.54  % (22337)------------------------------
% 0.21/0.54  % (22337)------------------------------
% 0.21/0.54  % (22346)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (22332)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (22349)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (22352)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (22346)Refutation not found, incomplete strategy% (22346)------------------------------
% 0.21/0.55  % (22346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22332)Refutation not found, incomplete strategy% (22332)------------------------------
% 0.21/0.55  % (22332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22346)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22346)Memory used [KB]: 6140
% 0.21/0.55  % (22346)Time elapsed: 0.148 s
% 0.21/0.55  % (22346)------------------------------
% 0.21/0.55  % (22346)------------------------------
% 0.21/0.55  % (22354)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (22351)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (22332)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22332)Memory used [KB]: 1663
% 0.21/0.55  % (22332)Time elapsed: 0.135 s
% 0.21/0.55  % (22332)------------------------------
% 0.21/0.55  % (22332)------------------------------
% 0.21/0.55  % (22354)Refutation not found, incomplete strategy% (22354)------------------------------
% 0.21/0.55  % (22354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22354)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22354)Memory used [KB]: 10618
% 0.21/0.55  % (22354)Time elapsed: 0.139 s
% 0.21/0.55  % (22354)------------------------------
% 0.21/0.55  % (22354)------------------------------
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (22351)# SZS output start Saturation.
% 0.21/0.55  tff(u90,negated_conjecture,
% 0.21/0.55      ((~(o_0_0_xboole_0 != sK0)) | (o_0_0_xboole_0 != sK0))).
% 0.21/0.55  
% 0.21/0.55  tff(u89,axiom,
% 0.21/0.55      ((~(o_0_0_xboole_0 = k1_xboole_0)) | (![X1, X0] : (((o_0_0_xboole_0 != k2_zfmisc_1(X0,X1)) | (o_0_0_xboole_0 = X1) | (o_0_0_xboole_0 = X0)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u88,axiom,
% 0.21/0.55      ((~(o_0_0_xboole_0 = k1_xboole_0)) | (o_0_0_xboole_0 = k1_xboole_0))).
% 0.21/0.55  
% 0.21/0.55  tff(u87,axiom,
% 0.21/0.55      ((~(o_0_0_xboole_0 = k1_xboole_0)) | (![X0] : ((o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u86,axiom,
% 0.21/0.55      ((~(o_0_0_xboole_0 = k1_xboole_0)) | (![X1] : ((o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u85,negated_conjecture,
% 0.21/0.55      ((~(o_0_0_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | (o_0_0_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)))).
% 0.21/0.55  
% 0.21/0.55  tff(u84,axiom,
% 0.21/0.55      ((~(o_0_0_xboole_0 = k1_xboole_0)) | (![X0] : ((~v1_xboole_0(X0) | (o_0_0_xboole_0 = X0)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u83,axiom,
% 0.21/0.55      ((~v1_xboole_0(o_0_0_xboole_0)) | v1_xboole_0(o_0_0_xboole_0))).
% 0.21/0.55  
% 0.21/0.55  % (22351)# SZS output end Saturation.
% 0.21/0.55  % (22351)------------------------------
% 0.21/0.55  % (22351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22351)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (22351)Memory used [KB]: 10746
% 0.21/0.55  % (22351)Time elapsed: 0.138 s
% 0.21/0.55  % (22351)------------------------------
% 0.21/0.55  % (22351)------------------------------
% 0.21/0.55  % (22334)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (22342)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (22345)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (22340)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (22334)Refutation not found, incomplete strategy% (22334)------------------------------
% 0.21/0.55  % (22334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22334)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22334)Memory used [KB]: 10618
% 0.21/0.55  % (22334)Time elapsed: 0.140 s
% 0.21/0.55  % (22334)------------------------------
% 0.21/0.55  % (22334)------------------------------
% 0.21/0.55  % (22340)Refutation not found, incomplete strategy% (22340)------------------------------
% 0.21/0.55  % (22340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22340)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22340)Memory used [KB]: 6268
% 0.21/0.55  % (22340)Time elapsed: 0.149 s
% 0.21/0.55  % (22340)------------------------------
% 0.21/0.55  % (22340)------------------------------
% 0.21/0.56  % (22357)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (22362)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (22357)Refutation not found, incomplete strategy% (22357)------------------------------
% 0.21/0.56  % (22357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22357)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22357)Memory used [KB]: 10618
% 0.21/0.56  % (22357)Time elapsed: 0.149 s
% 0.21/0.56  % (22357)------------------------------
% 0.21/0.56  % (22357)------------------------------
% 0.21/0.56  % (22362)Refutation not found, incomplete strategy% (22362)------------------------------
% 0.21/0.56  % (22362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22348)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.62/0.57  % (22341)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.62/0.57  % (22362)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.57  
% 1.62/0.57  % (22362)Memory used [KB]: 6140
% 1.62/0.57  % (22362)Time elapsed: 0.145 s
% 1.62/0.57  % (22362)------------------------------
% 1.62/0.57  % (22362)------------------------------
% 1.62/0.57  % (22328)Success in time 0.202 s
%------------------------------------------------------------------------------
