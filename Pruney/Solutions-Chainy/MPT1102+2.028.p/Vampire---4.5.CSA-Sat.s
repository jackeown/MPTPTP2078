%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:32 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   39 (  39 expanded)
%              Depth                    :    0
%              Number of atoms          :   73 (  73 expanded)
%              Number of equality atoms :   33 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u235,axiom,(
    ! [X1,X0] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) )).

tff(u234,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_xboole_0) ) )).

tff(u233,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != k9_subset_1(X1,X0,X1)
      | r1_tarski(X0,k4_xboole_0(X0,X1)) ) )).

tff(u232,axiom,(
    ! [X5,X4] :
      ( k1_xboole_0 != k9_subset_1(X5,X5,X4)
      | r1_tarski(X4,k4_xboole_0(X4,X5)) ) )).

tff(u231,negated_conjecture,
    ( ~ ( k1_xboole_0 != sK1 )
    | k1_xboole_0 != sK1 )).

tff(u230,negated_conjecture,
    ( ~ ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )
    | sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u229,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u228,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u227,axiom,(
    ! [X1] : k9_subset_1(X1,X1,X1) = X1 )).

tff(u226,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u225,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,u1_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u224,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u223,axiom,(
    ! [X1,X2] : k9_subset_1(X1,X2,X1) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) )).

tff(u222,axiom,(
    ! [X3,X2] : k9_subset_1(X2,X2,X3) = k4_xboole_0(X3,k4_xboole_0(X3,X2)) )).

tff(u221,axiom,(
    ! [X1,X2] : k9_subset_1(X1,X2,X1) = k9_subset_1(X1,X1,X2) )).

tff(u220,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(sK1,X0,sK1) )).

tff(u219,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k9_subset_1(u1_struct_0(sK0),sK1,X0) = k9_subset_1(sK1,X0,sK1) )).

tff(u218,axiom,(
    ! [X0] : k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0) )).

tff(u217,axiom,(
    ! [X2] : k1_xboole_0 = k9_subset_1(k1_xboole_0,k1_xboole_0,X2) )).

tff(u216,negated_conjecture,
    ( sK1 != k9_subset_1(sK1,sK1,u1_struct_0(sK0))
    | sK1 = k9_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

tff(u215,negated_conjecture,
    ( sK1 != k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | sK1 = k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u214,negated_conjecture,
    ( sK1 != k9_subset_1(sK1,u1_struct_0(sK0),sK1)
    | sK1 = k9_subset_1(sK1,u1_struct_0(sK0),sK1) )).

tff(u213,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

tff(u212,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK2(X0,X1),X2)
      | r1_tarski(X0,X1) ) )).

tff(u211,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u210,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1,X0] :
        ( ~ r1_tarski(u1_struct_0(sK0),X1)
        | r2_hidden(sK2(sK1,X0),X1)
        | r1_tarski(sK1,X0) ) )).

tff(u209,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u208,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u207,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u206,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u205,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,u1_struct_0(sK0)) ) )).

tff(u204,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u203,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( r2_hidden(sK2(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0) ) )).

tff(u202,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) )).

tff(u201,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) )).

tff(u200,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u199,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) )).

tff(u198,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u197,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:08:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (19979)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.48  % (19980)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.48  % (19995)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (19988)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (19995)Refutation not found, incomplete strategy% (19995)------------------------------
% 0.21/0.50  % (19995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19995)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19995)Memory used [KB]: 1663
% 0.21/0.50  % (19995)Time elapsed: 0.102 s
% 0.21/0.50  % (19995)------------------------------
% 0.21/0.50  % (19995)------------------------------
% 0.21/0.50  % (19990)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (19981)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (19982)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (19982)Refutation not found, incomplete strategy% (19982)------------------------------
% 0.21/0.50  % (19982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19982)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19982)Memory used [KB]: 10618
% 0.21/0.50  % (19982)Time elapsed: 0.100 s
% 0.21/0.50  % (19982)------------------------------
% 0.21/0.50  % (19982)------------------------------
% 0.21/0.51  % (19989)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (20000)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (19996)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (19974)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (19987)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (19985)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (19974)Refutation not found, incomplete strategy% (19974)------------------------------
% 0.21/0.51  % (19974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19974)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  % (19984)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  
% 0.21/0.51  % (19974)Memory used [KB]: 1663
% 0.21/0.51  % (19974)Time elapsed: 0.106 s
% 0.21/0.51  % (19974)------------------------------
% 0.21/0.51  % (19974)------------------------------
% 0.21/0.51  % (19997)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (19993)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (19984)Refutation not found, incomplete strategy% (19984)------------------------------
% 0.21/0.51  % (19984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19984)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19984)Memory used [KB]: 10618
% 0.21/0.51  % (19984)Time elapsed: 0.088 s
% 0.21/0.51  % (19984)------------------------------
% 0.21/0.51  % (19984)------------------------------
% 0.21/0.52  % (19975)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (19998)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (20001)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (19978)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (20002)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (19978)Refutation not found, incomplete strategy% (19978)------------------------------
% 0.21/0.52  % (19978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19978)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19978)Memory used [KB]: 6140
% 0.21/0.52  % (19978)Time elapsed: 0.109 s
% 0.21/0.52  % (19978)------------------------------
% 0.21/0.52  % (19978)------------------------------
% 0.21/0.52  % (19992)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (19990)# SZS output start Saturation.
% 0.21/0.52  tff(u235,axiom,
% 0.21/0.52      (![X1, X0] : (((k4_xboole_0(X0,X1) != k1_xboole_0) | r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u234,axiom,
% 0.21/0.52      (![X0] : (((k1_xboole_0 != X0) | r1_tarski(X0,k1_xboole_0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u233,axiom,
% 0.21/0.52      (![X1, X0] : (((k1_xboole_0 != k9_subset_1(X1,X0,X1)) | r1_tarski(X0,k4_xboole_0(X0,X1)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u232,axiom,
% 0.21/0.52      (![X5, X4] : (((k1_xboole_0 != k9_subset_1(X5,X5,X4)) | r1_tarski(X4,k4_xboole_0(X4,X5)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u231,negated_conjecture,
% 0.21/0.52      ((~(k1_xboole_0 != sK1)) | (k1_xboole_0 != sK1))).
% 0.21/0.52  
% 0.21/0.52  tff(u230,negated_conjecture,
% 0.21/0.52      ((~(sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))) | (sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u229,axiom,
% 0.21/0.52      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u228,axiom,
% 0.21/0.52      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u227,axiom,
% 0.21/0.52      (![X1] : ((k9_subset_1(X1,X1,X1) = X1)))).
% 0.21/0.52  
% 0.21/0.52  tff(u226,axiom,
% 0.21/0.52      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u225,negated_conjecture,
% 0.21/0.52      ((~(k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u224,negated_conjecture,
% 0.21/0.52      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u223,axiom,
% 0.21/0.52      (![X1, X2] : ((k9_subset_1(X1,X2,X1) = k4_xboole_0(X2,k4_xboole_0(X2,X1)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u222,axiom,
% 0.21/0.52      (![X3, X2] : ((k9_subset_1(X2,X2,X3) = k4_xboole_0(X3,k4_xboole_0(X3,X2)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u221,axiom,
% 0.21/0.52      (![X1, X2] : ((k9_subset_1(X1,X2,X1) = k9_subset_1(X1,X1,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u220,negated_conjecture,
% 0.21/0.52      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(sK1,X0,sK1)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u219,negated_conjecture,
% 0.21/0.52      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k9_subset_1(u1_struct_0(sK0),sK1,X0) = k9_subset_1(sK1,X0,sK1)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u218,axiom,
% 0.21/0.52      (![X0] : ((k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u217,axiom,
% 0.21/0.52      (![X2] : ((k1_xboole_0 = k9_subset_1(k1_xboole_0,k1_xboole_0,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u216,negated_conjecture,
% 0.21/0.52      ((~(sK1 = k9_subset_1(sK1,sK1,u1_struct_0(sK0)))) | (sK1 = k9_subset_1(sK1,sK1,u1_struct_0(sK0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u215,negated_conjecture,
% 0.21/0.52      ((~(sK1 = k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))) | (sK1 = k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u214,negated_conjecture,
% 0.21/0.52      ((~(sK1 = k9_subset_1(sK1,u1_struct_0(sK0),sK1))) | (sK1 = k9_subset_1(sK1,u1_struct_0(sK0),sK1)))).
% 0.21/0.52  
% 0.21/0.52  tff(u213,axiom,
% 0.21/0.52      (![X1, X2] : ((k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u212,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK2(X0,X1),X2) | r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u211,axiom,
% 0.21/0.52      (![X1, X0] : ((~r1_tarski(X0,X1) | (k4_xboole_0(X0,X1) = k1_xboole_0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u210,negated_conjecture,
% 0.21/0.52      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1, X0] : ((~r1_tarski(u1_struct_0(sK0),X1) | r2_hidden(sK2(sK1,X0),X1) | r1_tarski(sK1,X0)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u209,axiom,
% 0.21/0.52      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u208,negated_conjecture,
% 0.21/0.52      ((~r1_tarski(sK1,u1_struct_0(sK0))) | r1_tarski(sK1,u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u207,axiom,
% 0.21/0.52      (![X1, X0] : ((~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u206,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u205,negated_conjecture,
% 0.21/0.52      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~r2_hidden(X0,sK1) | r2_hidden(X0,u1_struct_0(sK0))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u204,axiom,
% 0.21/0.52      (![X1, X0] : ((r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u203,negated_conjecture,
% 0.21/0.52      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((r2_hidden(sK2(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u202,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u201,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u200,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u199,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u198,negated_conjecture,
% 0.21/0.52      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u197,axiom,
% 0.21/0.52      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.52  
% 0.21/0.52  % (19990)# SZS output end Saturation.
% 0.21/0.52  % (19990)------------------------------
% 0.21/0.52  % (19990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19990)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (19990)Memory used [KB]: 10746
% 0.21/0.52  % (19990)Time elapsed: 0.111 s
% 0.21/0.52  % (19990)------------------------------
% 0.21/0.52  % (19990)------------------------------
% 0.21/0.52  % (19973)Success in time 0.153 s
%------------------------------------------------------------------------------
