%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:29 EST 2020

% Result     : Timeout 57.20s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u56,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u55,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

tff(u54,axiom,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 )).

tff(u53,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

tff(u52,axiom,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5) )).

tff(u51,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) )).

tff(u50,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) )).

tff(u49,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u48,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:36:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (9842)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (9834)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (9837)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (9837)Refutation not found, incomplete strategy% (9837)------------------------------
% 0.21/0.48  % (9837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9837)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9837)Memory used [KB]: 10618
% 0.21/0.48  % (9837)Time elapsed: 0.072 s
% 0.21/0.48  % (9837)------------------------------
% 0.21/0.48  % (9837)------------------------------
% 0.21/0.49  % (9847)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (9845)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (9835)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (9833)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (9830)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (9832)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (9832)Refutation not found, incomplete strategy% (9832)------------------------------
% 0.21/0.50  % (9832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9832)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9832)Memory used [KB]: 1535
% 0.21/0.50  % (9832)Time elapsed: 0.093 s
% 0.21/0.50  % (9832)------------------------------
% 0.21/0.50  % (9832)------------------------------
% 0.21/0.50  % (9831)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (9831)Refutation not found, incomplete strategy% (9831)------------------------------
% 0.21/0.50  % (9831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9831)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9831)Memory used [KB]: 10618
% 0.21/0.50  % (9831)Time elapsed: 0.094 s
% 0.21/0.50  % (9831)------------------------------
% 0.21/0.50  % (9831)------------------------------
% 0.21/0.50  % (9844)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (9840)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (9829)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (9839)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (9847)Refutation not found, incomplete strategy% (9847)------------------------------
% 0.21/0.51  % (9847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9847)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9847)Memory used [KB]: 6140
% 0.21/0.51  % (9847)Time elapsed: 0.096 s
% 0.21/0.51  % (9847)------------------------------
% 0.21/0.51  % (9847)------------------------------
% 0.21/0.51  % (9836)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (9828)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (9829)Refutation not found, incomplete strategy% (9829)------------------------------
% 0.21/0.51  % (9829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9829)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9829)Memory used [KB]: 10490
% 0.21/0.51  % (9829)Time elapsed: 0.091 s
% 0.21/0.51  % (9829)------------------------------
% 0.21/0.51  % (9829)------------------------------
% 0.21/0.51  % (9839)Refutation not found, incomplete strategy% (9839)------------------------------
% 0.21/0.51  % (9839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9839)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9839)Memory used [KB]: 10618
% 0.21/0.51  % (9839)Time elapsed: 0.098 s
% 0.21/0.51  % (9839)------------------------------
% 0.21/0.51  % (9839)------------------------------
% 0.21/0.51  % (9828)Refutation not found, incomplete strategy% (9828)------------------------------
% 0.21/0.51  % (9828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9828)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9828)Memory used [KB]: 6140
% 0.21/0.51  % (9828)Time elapsed: 0.093 s
% 0.21/0.51  % (9828)------------------------------
% 0.21/0.51  % (9828)------------------------------
% 0.21/0.51  % (9841)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (9841)Refutation not found, incomplete strategy% (9841)------------------------------
% 0.21/0.51  % (9841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9841)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9841)Memory used [KB]: 1535
% 0.21/0.51  % (9841)Time elapsed: 0.086 s
% 0.21/0.51  % (9841)------------------------------
% 0.21/0.51  % (9841)------------------------------
% 0.21/0.51  % (9840)Refutation not found, incomplete strategy% (9840)------------------------------
% 0.21/0.51  % (9840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9840)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9840)Memory used [KB]: 6012
% 0.21/0.51  % (9840)Time elapsed: 0.003 s
% 0.21/0.51  % (9840)------------------------------
% 0.21/0.51  % (9840)------------------------------
% 0.21/0.51  % (9838)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (9838)Refutation not found, incomplete strategy% (9838)------------------------------
% 0.21/0.51  % (9838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9838)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9838)Memory used [KB]: 6012
% 0.21/0.51  % (9838)Time elapsed: 0.106 s
% 0.21/0.51  % (9838)------------------------------
% 0.21/0.51  % (9838)------------------------------
% 0.21/0.52  % (9846)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (9846)Refutation not found, incomplete strategy% (9846)------------------------------
% 0.21/0.52  % (9846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9846)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9846)Memory used [KB]: 1663
% 0.21/0.52  % (9846)Time elapsed: 0.107 s
% 0.21/0.52  % (9846)------------------------------
% 0.21/0.52  % (9846)------------------------------
% 0.21/0.52  % (9848)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (9848)Refutation not found, incomplete strategy% (9848)------------------------------
% 0.21/0.52  % (9848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9848)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9848)Memory used [KB]: 10490
% 0.21/0.52  % (9848)Time elapsed: 0.104 s
% 0.21/0.52  % (9848)------------------------------
% 0.21/0.52  % (9848)------------------------------
% 0.21/0.53  % (9843)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (9843)Refutation not found, incomplete strategy% (9843)------------------------------
% 0.21/0.53  % (9843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9843)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9843)Memory used [KB]: 6012
% 0.21/0.53  % (9843)Time elapsed: 0.116 s
% 0.21/0.53  % (9843)------------------------------
% 0.21/0.53  % (9843)------------------------------
% 4.51/0.94  % (9833)Time limit reached!
% 4.51/0.94  % (9833)------------------------------
% 4.51/0.94  % (9833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/0.94  % (9833)Termination reason: Time limit
% 4.51/0.94  % (9833)Termination phase: Saturation
% 4.51/0.94  
% 4.51/0.94  % (9833)Memory used [KB]: 8955
% 4.51/0.94  % (9833)Time elapsed: 0.500 s
% 4.51/0.94  % (9833)------------------------------
% 4.51/0.94  % (9833)------------------------------
% 4.75/1.01  % (9836)Time limit reached!
% 4.75/1.01  % (9836)------------------------------
% 4.75/1.01  % (9836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.75/1.01  % (9836)Termination reason: Time limit
% 4.75/1.01  % (9836)Termination phase: Saturation
% 4.75/1.01  
% 4.75/1.01  % (9836)Memory used [KB]: 10362
% 4.75/1.01  % (9836)Time elapsed: 0.600 s
% 4.75/1.01  % (9836)------------------------------
% 4.75/1.01  % (9836)------------------------------
% 7.95/1.52  % (9830)Time limit reached!
% 7.95/1.52  % (9830)------------------------------
% 7.95/1.52  % (9830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.95/1.52  % (9830)Termination reason: Time limit
% 7.95/1.52  % (9830)Termination phase: Saturation
% 7.95/1.52  
% 7.95/1.52  % (9830)Memory used [KB]: 15991
% 7.95/1.52  % (9830)Time elapsed: 1.100 s
% 7.95/1.52  % (9830)------------------------------
% 7.95/1.52  % (9830)------------------------------
% 11.16/2.11  % (9835)Time limit reached!
% 11.16/2.11  % (9835)------------------------------
% 11.16/2.11  % (9835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.16/2.11  % (9835)Termination reason: Time limit
% 11.16/2.11  % (9835)Termination phase: Saturation
% 11.16/2.11  
% 11.16/2.11  % (9835)Memory used [KB]: 10490
% 11.16/2.11  % (9835)Time elapsed: 1.700 s
% 11.16/2.11  % (9835)------------------------------
% 11.16/2.11  % (9835)------------------------------
% 24.90/5.57  % (9834)Time limit reached!
% 24.90/5.57  % (9834)------------------------------
% 24.90/5.57  % (9834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.90/5.57  % (9834)Termination reason: Time limit
% 24.90/5.57  % (9834)Termination phase: Saturation
% 24.90/5.57  
% 24.90/5.57  % (9834)Memory used [KB]: 41321
% 24.90/5.57  % (9834)Time elapsed: 5.100 s
% 24.90/5.57  % (9834)------------------------------
% 24.90/5.57  % (9834)------------------------------
% 27.38/6.40  % (9844)Time limit reached!
% 27.38/6.40  % (9844)------------------------------
% 27.38/6.40  % (9844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 27.38/6.40  % (9844)Termination reason: Time limit
% 27.38/6.40  % (9844)Termination phase: Saturation
% 27.38/6.40  
% 27.38/6.40  % (9844)Memory used [KB]: 32750
% 27.38/6.40  % (9844)Time elapsed: 6.0000 s
% 27.38/6.40  % (9844)------------------------------
% 27.38/6.40  % (9844)------------------------------
% 49.70/17.38  % (9842)Time limit reached!
% 49.70/17.38  % (9842)------------------------------
% 49.70/17.38  % (9842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 49.70/17.38  % (9842)Termination reason: Time limit
% 49.70/17.38  % (9842)Termination phase: Saturation
% 49.70/17.38  
% 49.70/17.38  % (9842)Memory used [KB]: 326220
% 49.70/17.38  % (9842)Time elapsed: 16.900 s
% 49.70/17.38  % (9842)------------------------------
% 49.70/17.38  % (9842)------------------------------
% 56.39/23.91  % (9845)Time limit reached!
% 56.39/23.91  % (9845)------------------------------
% 56.39/23.91  % (9845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.39/23.91  % (9845)Termination reason: Time limit
% 56.39/23.91  % (9845)Termination phase: Saturation
% 56.39/23.91  
% 56.39/23.91  % (9845)Memory used [KB]: 40681
% 56.39/23.91  % (9845)Time elapsed: 23.500 s
% 56.39/23.91  % (9845)------------------------------
% 56.39/23.91  % (9845)------------------------------
% 56.42/24.00  % (10681)lrs+1_4_afp=100000:afq=1.2:anc=none:bd=off:cond=on:gs=on:gsem=off:nm=64:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:updr=off_300 on theBenchmark
% 56.42/24.00  % (10681)Refutation not found, incomplete strategy% (10681)------------------------------
% 56.42/24.00  % (10681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.42/24.00  % (10681)Termination reason: Refutation not found, incomplete strategy
% 56.42/24.00  
% 56.42/24.00  % (10681)Memory used [KB]: 10618
% 56.42/24.00  % (10681)Time elapsed: 0.063 s
% 56.42/24.00  % (10681)------------------------------
% 56.42/24.00  % (10681)------------------------------
% 56.42/24.01  % (10697)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:sp=occurrence:urr=on_300 on theBenchmark
% 56.42/24.01  % (10689)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence_300 on theBenchmark
% 56.42/24.01  % (10689)Refutation not found, incomplete strategy% (10689)------------------------------
% 56.42/24.01  % (10689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.42/24.01  % (10689)Termination reason: Refutation not found, incomplete strategy
% 56.42/24.01  
% 56.42/24.01  % (10689)Memory used [KB]: 10490
% 56.42/24.01  % (10689)Time elapsed: 0.074 s
% 56.42/24.01  % (10689)------------------------------
% 56.42/24.01  % (10689)------------------------------
% 56.48/24.09  % (10683)lrs+1011_2:1_av=off:irw=on:lwlo=on:nm=16:newcnf=on:nwc=2:sd=4:ss=axioms:st=3.0:sp=occurrence_300 on theBenchmark
% 56.48/24.09  % (10704)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_300 on theBenchmark
% 56.48/24.09  % (10710)lrs+11_8:1_av=off:bd=off:bs=unit_only:gs=on:gsem=on:lma=on:lwlo=on:nm=0:nwc=1:sd=1:ss=axioms:sos=all:urr=on:updr=off_300 on theBenchmark
% 56.48/24.09  % (10710)Refutation not found, incomplete strategy% (10710)------------------------------
% 56.48/24.09  % (10710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.09  % (10682)dis+1002_4_add=large:afp=40000:afq=1.0:anc=none:cond=fast:fde=none:gs=on:gsaa=full_model:lma=on:lwlo=on:nm=0:nwc=1.5:sas=z3:sp=reverse_arity:tha=off:thi=strong_300 on theBenchmark
% 56.48/24.09  % (10710)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.09  
% 56.48/24.09  % (10710)Memory used [KB]: 6012
% 56.48/24.09  % (10710)Time elapsed: 0.043 s
% 56.48/24.09  % (10710)------------------------------
% 56.48/24.09  % (10710)------------------------------
% 56.48/24.10  % (10687)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_300 on theBenchmark
% 56.48/24.10  % (10680)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:sac=on:sp=occurrence_300 on theBenchmark
% 56.48/24.10  % (10684)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:sp=occurrence_300 on theBenchmark
% 56.48/24.10  % (10695)dis+1010_2:3_add=off:afr=on:afp=10000:afq=1.1:anc=none:fsr=off:gs=on:gsem=off:nwc=1:sas=z3:sos=all:sac=on:sp=reverse_arity:tha=off_300 on theBenchmark
% 56.48/24.10  % (10703)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:sp=reverse_arity:updr=off_300 on theBenchmark
% 56.48/24.10  % (10684)Refutation not found, incomplete strategy% (10684)------------------------------
% 56.48/24.10  % (10684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.10  % (10684)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.10  
% 56.48/24.10  % (10684)Memory used [KB]: 1663
% 56.48/24.10  % (10684)Time elapsed: 0.129 s
% 56.48/24.10  % (10684)------------------------------
% 56.48/24.10  % (10684)------------------------------
% 56.48/24.10  % (10691)lrs+10_5:4_av=off:cond=on:fde=unused:gs=on:gsem=on:lcm=reverse:lma=on:lwlo=on:nm=32:nwc=1.7:sd=2:ss=axioms:st=2.0:sos=all_300 on theBenchmark
% 56.48/24.10  % (10691)Refutation not found, incomplete strategy% (10691)------------------------------
% 56.48/24.10  % (10691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.10  % (10691)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.10  
% 56.48/24.10  % (10691)Memory used [KB]: 6012
% 56.48/24.10  % (10691)Time elapsed: 0.139 s
% 56.48/24.10  % (10691)------------------------------
% 56.48/24.10  % (10691)------------------------------
% 56.48/24.10  % (10693)lrs+1_1024_av=off:bs=on:fde=none:inw=on:irw=on:nm=64:nwc=1.2:sp=reverse_arity:tha=off:urr=on:updr=off:uhcvi=on_600 on theBenchmark
% 56.48/24.10  % (10707)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_300 on theBenchmark
% 56.48/24.10  % (10688)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:sos=all:sp=occurrence:urr=on_300 on theBenchmark
% 56.48/24.11  % (10686)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:sos=all:sp=reverse_arity:updr=off_300 on theBenchmark
% 56.48/24.11  % (10686)Refutation not found, incomplete strategy% (10686)------------------------------
% 56.48/24.11  % (10686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.11  % (10686)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.11  
% 56.48/24.11  % (10686)Memory used [KB]: 6012
% 56.48/24.11  % (10686)Time elapsed: 0.001 s
% 56.48/24.11  % (10686)------------------------------
% 56.48/24.11  % (10686)------------------------------
% 56.48/24.11  % (10706)dis+1011_2:3_add=off:afr=on:afp=4000:afq=1.4:anc=none:bs=unit_only:fsr=off:gs=on:gsem=on:lwlo=on:nm=16:nwc=1.3:nicw=on:sas=z3:sac=on:tha=off_300 on theBenchmark
% 56.48/24.11  % (10711)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_300 on theBenchmark
% 56.48/24.11  % (10688)Refutation not found, incomplete strategy% (10688)------------------------------
% 56.48/24.11  % (10688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.11  % (10692)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_300 on theBenchmark
% 56.48/24.11  % (10688)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.11  
% 56.48/24.11  % (10688)Memory used [KB]: 10618
% 56.48/24.11  % (10688)Time elapsed: 0.145 s
% 56.48/24.11  % (10688)------------------------------
% 56.48/24.11  % (10688)------------------------------
% 56.48/24.11  % (10700)dis+11_32_av=off:ep=RST:fsr=off:lwlo=on:nm=6:nwc=1.1:sd=5:ss=axioms:st=5.0:sp=reverse_arity:uhcvi=on_1500 on theBenchmark
% 56.48/24.11  % (10702)lrs+11_50_afp=100000:afq=1.1:amm=sco:anc=none:bs=unit_only:cond=on:irw=on:lma=on:nm=32:nwc=1.1:sp=reverse_arity_300 on theBenchmark
% 56.48/24.11  % (10711)Refutation not found, incomplete strategy% (10711)------------------------------
% 56.48/24.11  % (10711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.11  % (10711)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.11  
% 56.48/24.11  % (10711)Memory used [KB]: 1535
% 56.48/24.11  % (10711)Time elapsed: 0.047 s
% 56.48/24.11  % (10711)------------------------------
% 56.48/24.11  % (10711)------------------------------
% 56.48/24.11  % (10698)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_300 on theBenchmark
% 56.48/24.11  % (10683)Refutation not found, incomplete strategy% (10683)------------------------------
% 56.48/24.11  % (10683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.11  % (10683)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.11  
% 56.48/24.11  % (10683)Memory used [KB]: 1663
% 56.48/24.11  % (10683)Time elapsed: 0.148 s
% 56.48/24.11  % (10683)------------------------------
% 56.48/24.11  % (10683)------------------------------
% 56.48/24.11  % (10704)Refutation not found, incomplete strategy% (10704)------------------------------
% 56.48/24.11  % (10704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.11  % (10704)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.11  
% 56.48/24.11  % (10704)Memory used [KB]: 6140
% 56.48/24.11  % (10704)Time elapsed: 0.134 s
% 56.48/24.11  % (10704)------------------------------
% 56.48/24.11  % (10704)------------------------------
% 56.48/24.11  % (10698)Refutation not found, incomplete strategy% (10698)------------------------------
% 56.48/24.11  % (10698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.11  % (10698)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.11  
% 56.48/24.11  % (10698)Memory used [KB]: 6140
% 56.48/24.11  % (10698)Time elapsed: 0.149 s
% 56.48/24.11  % (10698)------------------------------
% 56.48/24.11  % (10698)------------------------------
% 56.48/24.11  % (10701)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_300 on theBenchmark
% 56.48/24.11  % (10709)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:sd=2:ss=axioms:st=1.5:sos=on_300 on theBenchmark
% 56.48/24.11  % (10699)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_300 on theBenchmark
% 56.48/24.11  % (10701)Refutation not found, incomplete strategy% (10701)------------------------------
% 56.48/24.11  % (10701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.11  % (10701)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.11  
% 56.48/24.11  % (10701)Memory used [KB]: 6012
% 56.48/24.11  % (10701)Time elapsed: 0.152 s
% 56.48/24.11  % (10701)------------------------------
% 56.48/24.11  % (10701)------------------------------
% 56.48/24.11  % (10709)Refutation not found, incomplete strategy% (10709)------------------------------
% 56.48/24.11  % (10709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.11  % (10709)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.11  
% 56.48/24.11  % (10709)Memory used [KB]: 10490
% 56.48/24.11  % (10709)Time elapsed: 0.152 s
% 56.48/24.11  % (10709)------------------------------
% 56.48/24.11  % (10709)------------------------------
% 56.48/24.11  % (10694)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_300 on theBenchmark
% 56.48/24.11  % (10685)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:sac=on_900 on theBenchmark
% 56.48/24.11  % (10690)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_300 on theBenchmark
% 56.48/24.11  % (10694)Refutation not found, incomplete strategy% (10694)------------------------------
% 56.48/24.11  % (10694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.11  % (10694)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.11  
% 56.48/24.11  % (10694)Memory used [KB]: 6012
% 56.48/24.11  % (10694)Time elapsed: 0.150 s
% 56.48/24.11  % (10694)------------------------------
% 56.48/24.11  % (10694)------------------------------
% 56.48/24.12  % (10690)Refutation not found, incomplete strategy% (10690)------------------------------
% 56.48/24.12  % (10690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.12  % (10690)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.12  
% 56.48/24.12  % (10690)Memory used [KB]: 10618
% 56.48/24.12  % (10690)Time elapsed: 0.153 s
% 56.48/24.12  % (10690)------------------------------
% 56.48/24.12  % (10690)------------------------------
% 56.48/24.12  % (10705)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_300 on theBenchmark
% 56.48/24.12  % (10708)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_300 on theBenchmark
% 56.48/24.12  % (10708)Refutation not found, incomplete strategy% (10708)------------------------------
% 56.48/24.12  % (10708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.12  % (10708)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.12  
% 56.48/24.12  % (10708)Memory used [KB]: 10618
% 56.48/24.12  % (10708)Time elapsed: 0.149 s
% 56.48/24.12  % (10708)------------------------------
% 56.48/24.12  % (10708)------------------------------
% 56.48/24.12  % (10705)Refutation not found, incomplete strategy% (10705)------------------------------
% 56.48/24.12  % (10705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.13  % (10696)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_300 on theBenchmark
% 56.48/24.13  % (10707)Refutation not found, incomplete strategy% (10707)------------------------------
% 56.48/24.13  % (10707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 56.48/24.13  % (10707)Termination reason: Refutation not found, incomplete strategy
% 56.48/24.13  
% 56.48/24.13  % (10707)Memory used [KB]: 1535
% 56.48/24.13  % (10707)Time elapsed: 0.002 s
% 56.48/24.13  % (10707)------------------------------
% 56.48/24.13  % (10707)------------------------------
% 57.20/24.13  % (10705)Termination reason: Refutation not found, incomplete strategy
% 57.20/24.13  
% 57.20/24.13  % (10705)Memory used [KB]: 6140
% 57.20/24.13  % (10705)Time elapsed: 0.146 s
% 57.20/24.13  % (10705)------------------------------
% 57.20/24.13  % (10705)------------------------------
% 57.20/24.19  % (10712)ott+1002_128_av=off:bd=off:bs=on:bsr=on:cond=on:fsr=off:nm=6:newcnf=on:nwc=1:sp=reverse_arity:updr=off_300 on theBenchmark
% 57.25/24.20  % (10712)Refutation not found, incomplete strategy% (10712)------------------------------
% 57.25/24.20  % (10712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.25/24.20  % (10712)Termination reason: Refutation not found, incomplete strategy
% 57.25/24.20  
% 57.25/24.20  % (10712)Memory used [KB]: 1663
% 57.25/24.20  % (10712)Time elapsed: 0.057 s
% 57.25/24.20  % (10712)------------------------------
% 57.25/24.20  % (10712)------------------------------
% 57.25/24.21  % (10714)ott-11_3_add=large:afp=100000:afq=1.2:anc=none:bs=on:cond=fast:fde=none:gs=on:gsem=off:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1:sos=all:sp=occurrence:tha=off:urr=on:uhcvi=on_300 on theBenchmark
% 57.25/24.21  % (10715)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_300 on theBenchmark
% 57.25/24.21  % (10715)Refutation not found, incomplete strategy% (10715)------------------------------
% 57.25/24.21  % (10715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.25/24.21  % (10715)Termination reason: Refutation not found, incomplete strategy
% 57.25/24.21  
% 57.25/24.21  % (10715)Memory used [KB]: 10618
% 57.25/24.21  % (10715)Time elapsed: 0.060 s
% 57.25/24.21  % (10715)------------------------------
% 57.25/24.21  % (10715)------------------------------
% 57.25/24.23  % (10714)Refutation not found, incomplete strategy% (10714)------------------------------
% 57.25/24.23  % (10714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.25/24.23  % (10714)Termination reason: Refutation not found, incomplete strategy
% 57.25/24.23  
% 57.25/24.23  % (10714)Memory used [KB]: 10618
% 57.25/24.23  % (10714)Time elapsed: 0.092 s
% 57.25/24.23  % (10714)------------------------------
% 57.25/24.23  % (10714)------------------------------
% 57.25/24.23  % (10713)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_300 on theBenchmark
% 57.25/24.23  % (10717)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_300 on theBenchmark
% 57.25/24.23  % (10717)Refutation not found, incomplete strategy% (10717)------------------------------
% 57.25/24.23  % (10717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.25/24.23  % (10717)Termination reason: Refutation not found, incomplete strategy
% 57.25/24.23  
% 57.25/24.23  % (10717)Memory used [KB]: 6012
% 57.25/24.23  % (10717)Time elapsed: 0.002 s
% 57.25/24.23  % (10717)------------------------------
% 57.25/24.23  % (10717)------------------------------
% 57.25/24.23  % (10719)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_300 on theBenchmark
% 57.25/24.24  % (10695)Refutation not found, incomplete strategy% (10695)------------------------------
% 57.25/24.24  % (10695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.25/24.24  % (10695)Termination reason: Refutation not found, incomplete strategy
% 57.25/24.24  
% 57.25/24.24  % (10695)Memory used [KB]: 6140
% 57.25/24.24  % (10695)Time elapsed: 0.230 s
% 57.25/24.24  % (10695)------------------------------
% 57.25/24.24  % (10695)------------------------------
% 57.25/24.24  % (10716)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:sp=occurrence:urr=on:updr=off_300 on theBenchmark
% 57.25/24.24  % (10682)Refutation not found, incomplete strategy% (10682)------------------------------
% 57.25/24.24  % (10682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.25/24.24  % (10682)Termination reason: Refutation not found, incomplete strategy
% 57.25/24.24  
% 57.25/24.24  % (10682)Memory used [KB]: 6140
% 57.25/24.24  % (10682)Time elapsed: 0.269 s
% 57.25/24.24  % (10682)------------------------------
% 57.25/24.24  % (10682)------------------------------
% 57.25/24.24  % (10722)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_600 on theBenchmark
% 57.25/24.25  % (10721)lrs+1011_1_av=off:cond=on:gs=on:lma=on:nm=4:nwc=1:sd=3:ss=axioms:sos=all:sp=reverse_arity:updr=off_300 on theBenchmark
% 57.25/24.25  % (10723)lrs+1002_2:1_acc=on:add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:ccuc=first:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1:sd=2:ss=axioms:sos=on:sp=reverse_arity_300 on theBenchmark
% 57.25/24.25  % (10721)Refutation not found, incomplete strategy% (10721)------------------------------
% 57.25/24.25  % (10721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.25/24.25  % (10721)Termination reason: Refutation not found, incomplete strategy
% 57.25/24.25  
% 57.25/24.25  % (10721)Memory used [KB]: 6140
% 57.25/24.25  % (10721)Time elapsed: 0.109 s
% 57.25/24.25  % (10721)------------------------------
% 57.25/24.25  % (10721)------------------------------
% 57.25/24.25  % (10720)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:sos=on:sac=on:sp=reverse_arity:updr=off_300 on theBenchmark
% 57.25/24.25  % (10718)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:sd=2:ss=axioms:st=1.5:updr=off_300 on theBenchmark
% 57.25/24.25  % (10723)Refutation not found, incomplete strategy% (10723)------------------------------
% 57.25/24.25  % (10723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.25/24.25  % (10723)Termination reason: Refutation not found, incomplete strategy
% 57.25/24.25  
% 57.25/24.25  % (10723)Memory used [KB]: 10490
% 57.25/24.25  % (10723)Time elapsed: 0.107 s
% 57.25/24.25  % (10723)------------------------------
% 57.25/24.25  % (10723)------------------------------
% 57.25/24.25  % (10720)Refutation not found, incomplete strategy% (10720)------------------------------
% 57.25/24.25  % (10720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.25/24.25  % (10720)Termination reason: Refutation not found, incomplete strategy
% 57.25/24.25  
% 57.25/24.25  % (10720)Memory used [KB]: 10618
% 57.25/24.25  % (10720)Time elapsed: 0.121 s
% 57.25/24.25  % (10720)------------------------------
% 57.25/24.25  % (10720)------------------------------
% 57.25/24.25  % (10687)Refutation not found, incomplete strategy% (10687)------------------------------
% 57.25/24.25  % (10687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.25/24.25  % (10687)Termination reason: Refutation not found, incomplete strategy
% 57.25/24.25  
% 57.25/24.25  % (10687)Memory used [KB]: 6140
% 57.25/24.25  % (10687)Time elapsed: 0.276 s
% 57.25/24.25  % (10687)------------------------------
% 57.25/24.25  % (10687)------------------------------
% 57.25/24.25  % (10724)ott+11_2:1_av=off:bd=off:bsr=on:br=off:cond=on:fsr=off:gsp=input_only:lma=on:nm=32:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_300 on theBenchmark
% 57.25/24.25  % (10724)Refutation not found, incomplete strategy% (10724)------------------------------
% 57.25/24.25  % (10724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.25/24.25  % (10724)Termination reason: Refutation not found, incomplete strategy
% 57.25/24.25  
% 57.25/24.25  % (10724)Memory used [KB]: 1535
% 57.25/24.25  % (10724)Time elapsed: 0.117 s
% 57.25/24.25  % (10724)------------------------------
% 57.25/24.25  % (10724)------------------------------
% 57.69/24.26  % (10726)dis+11_3_add=off:afp=10000:afq=2.0:amm=sco:anc=none:ep=RST:gs=on:gsaa=from_current:gsem=on:inw=on:nm=64:nwc=1:sd=10:ss=axioms:st=5.0:sos=all:tha=off:updr=off:uhcvi=on_300 on theBenchmark
% 57.69/24.26  % (10727)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_300 on theBenchmark
% 57.69/24.27  % (10692)Refutation not found, incomplete strategy% (10692)------------------------------
% 57.69/24.27  % (10692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.69/24.27  % (10692)Termination reason: Refutation not found, incomplete strategy
% 57.69/24.27  
% 57.69/24.27  % (10692)Memory used [KB]: 6140
% 57.69/24.27  % (10692)Time elapsed: 0.288 s
% 57.69/24.27  % (10692)------------------------------
% 57.69/24.27  % (10692)------------------------------
% 59.00/24.27  % (10725)ott+11_3_afp=1000:afq=2.0:anc=none:fsr=off:irw=on:nwc=1.7:ss=axioms:st=1.5:sac=on:updr=off_300 on theBenchmark
% 59.00/24.28  % (10727)Refutation not found, incomplete strategy% (10727)------------------------------
% 59.00/24.28  % (10727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 59.00/24.28  % (10727)Termination reason: Refutation not found, incomplete strategy
% 59.00/24.28  
% 59.00/24.28  % (10727)Memory used [KB]: 6012
% 59.00/24.28  % (10727)Time elapsed: 0.003 s
% 59.00/24.28  % (10727)------------------------------
% 59.00/24.28  % (10727)------------------------------
% 59.00/24.29  % (10728)ott+1010_5:4_av=off:bd=off:fde=none:irw=on:lma=on:nm=32:nwc=2.5:sd=2:ss=axioms:st=3.0:urr=on_300 on theBenchmark
% 59.31/24.32  % SZS status CounterSatisfiable for theBenchmark
% 59.31/24.33  % (10722)# SZS output start Saturation.
% 59.31/24.33  tff(u56,axiom,
% 59.31/24.33      (![X0] : ((k2_xboole_0(X0,k1_xboole_0) = X0)))).
% 59.31/24.33  
% 59.31/24.33  tff(u55,axiom,
% 59.31/24.33      (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0))))).
% 59.31/24.33  
% 59.31/24.33  tff(u54,axiom,
% 59.31/24.33      (![X0] : ((k2_xboole_0(k1_xboole_0,X0) = X0)))).
% 59.31/24.33  
% 59.31/24.33  tff(u53,axiom,
% 59.31/24.33      (![X0] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0))))).
% 59.31/24.33  
% 59.31/24.33  tff(u52,axiom,
% 59.31/24.33      (![X5] : ((k1_xboole_0 = k4_xboole_0(X5,X5))))).
% 59.31/24.33  
% 59.31/24.33  tff(u51,axiom,
% 59.31/24.33      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1))))).
% 59.31/24.33  
% 59.31/24.33  tff(u50,axiom,
% 59.31/24.33      (![X1, X2] : ((k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2))))).
% 59.31/24.33  
% 59.31/24.33  tff(u49,axiom,
% 59.31/24.33      (![X1, X0] : ((~r1_tarski(X0,X1) | (k4_xboole_0(X0,X1) = k1_xboole_0))))).
% 59.31/24.33  
% 59.31/24.33  tff(u48,axiom,
% 59.31/24.33      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 59.31/24.33  
% 59.31/24.33  % (10722)# SZS output end Saturation.
% 59.31/24.33  % (10722)------------------------------
% 59.31/24.33  % (10722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 59.31/24.33  % (10722)Termination reason: Satisfiable
% 59.31/24.33  
% 59.31/24.33  % (10722)Memory used [KB]: 6140
% 59.31/24.33  % (10722)Time elapsed: 0.181 s
% 59.31/24.33  % (10722)------------------------------
% 59.31/24.33  % (10722)------------------------------
% 59.31/24.33  % (9825)Success in time 23.971 s
%------------------------------------------------------------------------------
