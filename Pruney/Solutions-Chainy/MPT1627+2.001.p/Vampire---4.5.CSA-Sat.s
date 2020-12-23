%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:55 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   59 (  59 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u89,axiom,(
    ! [X1,X0] :
      ( ~ v2_struct_0(X0)
      | ~ sQ3_eqProxy(X0,X1)
      | v2_struct_0(X1) ) )).

tff(u88,axiom,(
    ! [X1,X0] :
      ( ~ v4_orders_2(X0)
      | ~ sQ3_eqProxy(X0,X1)
      | v4_orders_2(X1) ) )).

tff(u87,axiom,(
    ! [X1,X0] :
      ( ~ l1_orders_2(X0)
      | ~ sQ3_eqProxy(X0,X1)
      | l1_orders_2(X1) ) )).

tff(u86,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ v4_yellow_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | v4_yellow_0(X1,X3) ) )).

tff(u85,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_yellow_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | m1_yellow_0(X1,X3) ) )).

tff(u84,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | m1_subset_1(X1,X3) ) )).

tff(u83,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK1,sK2)
    | ~ r1_yellow_0(sK1,sK2) )).

tff(u82,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_yellow_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | r1_yellow_0(X1,X3) ) )).

tff(u81,negated_conjecture,(
    r1_yellow_0(sK0,sK2) )).

tff(u80,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | r2_hidden(X1,X3) ) )).

tff(u79,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ v4_waybel_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | v4_waybel_0(X1,X3) ) )).

tff(u78,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ v1_waybel_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | v1_waybel_0(X1,X3) ) )).

tff(u77,axiom,(
    ! [X1,X0,X2] :
      ( ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X0,X2) ) )).

tff(u76,axiom,(
    ! [X1,X0] :
      ( ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X1,X0) ) )).

tff(u75,negated_conjecture,(
    ~ sQ3_eqProxy(k1_xboole_0,sK2) )).

tff(u74,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK1,sK2)
    | ~ sQ3_eqProxy(sK0,sK1) )).

tff(u73,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK1,sK2)
    | ~ sQ3_eqProxy(sK1,sK0) )).

tff(u72,negated_conjecture,(
    ~ sQ3_eqProxy(sK2,k1_xboole_0) )).

tff(u71,axiom,(
    ! [X0] : sQ3_eqProxy(X0,X0) )).

tff(u70,axiom,(
    ! [X1,X0] :
      ( sQ3_eqProxy(u1_struct_0(X0),u1_struct_0(X1))
      | ~ sQ3_eqProxy(X0,X1) ) )).

tff(u69,axiom,(
    ! [X1,X0] :
      ( sQ3_eqProxy(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ sQ3_eqProxy(X0,X1) ) )).

tff(u68,axiom,(
    ! [X1,X3,X0,X2] :
      ( sQ3_eqProxy(k1_yellow_0(X0,X2),k1_yellow_0(X1,X3))
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:59:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (7950)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (7950)Refutation not found, incomplete strategy% (7950)------------------------------
% 0.22/0.47  % (7950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7956)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (7950)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7950)Memory used [KB]: 10490
% 0.22/0.48  % (7950)Time elapsed: 0.049 s
% 0.22/0.48  % (7950)------------------------------
% 0.22/0.48  % (7950)------------------------------
% 0.22/0.48  % (7956)Refutation not found, incomplete strategy% (7956)------------------------------
% 0.22/0.48  % (7956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7956)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7956)Memory used [KB]: 6012
% 0.22/0.48  % (7956)Time elapsed: 0.004 s
% 0.22/0.48  % (7956)------------------------------
% 0.22/0.48  % (7956)------------------------------
% 0.22/0.51  % (7965)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (7965)Refutation not found, incomplete strategy% (7965)------------------------------
% 0.22/0.51  % (7965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7965)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7965)Memory used [KB]: 10490
% 0.22/0.51  % (7965)Time elapsed: 0.090 s
% 0.22/0.51  % (7965)------------------------------
% 0.22/0.51  % (7965)------------------------------
% 0.22/0.52  % (7949)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (7946)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (7954)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (7954)Refutation not found, incomplete strategy% (7954)------------------------------
% 0.22/0.52  % (7954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7954)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7954)Memory used [KB]: 6012
% 0.22/0.52  % (7954)Time elapsed: 0.072 s
% 0.22/0.52  % (7954)------------------------------
% 0.22/0.52  % (7954)------------------------------
% 0.22/0.52  % (7946)Refutation not found, incomplete strategy% (7946)------------------------------
% 0.22/0.52  % (7946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7946)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7946)Memory used [KB]: 10490
% 0.22/0.52  % (7946)Time elapsed: 0.073 s
% 0.22/0.52  % (7946)------------------------------
% 0.22/0.52  % (7946)------------------------------
% 0.22/0.53  % (7958)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (7958)# SZS output start Saturation.
% 0.22/0.53  tff(u89,axiom,
% 0.22/0.53      (![X1, X0] : ((~v2_struct_0(X0) | ~sQ3_eqProxy(X0,X1) | v2_struct_0(X1))))).
% 0.22/0.53  
% 0.22/0.53  tff(u88,axiom,
% 0.22/0.53      (![X1, X0] : ((~v4_orders_2(X0) | ~sQ3_eqProxy(X0,X1) | v4_orders_2(X1))))).
% 0.22/0.53  
% 0.22/0.53  tff(u87,axiom,
% 0.22/0.53      (![X1, X0] : ((~l1_orders_2(X0) | ~sQ3_eqProxy(X0,X1) | l1_orders_2(X1))))).
% 0.22/0.53  
% 0.22/0.53  tff(u86,axiom,
% 0.22/0.53      (![X1, X3, X0, X2] : ((~v4_yellow_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | v4_yellow_0(X1,X3))))).
% 0.22/0.53  
% 0.22/0.53  tff(u85,axiom,
% 0.22/0.53      (![X1, X3, X0, X2] : ((~m1_yellow_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | m1_yellow_0(X1,X3))))).
% 0.22/0.53  
% 0.22/0.53  tff(u84,axiom,
% 0.22/0.53      (![X1, X3, X0, X2] : ((~m1_subset_1(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | m1_subset_1(X1,X3))))).
% 0.22/0.53  
% 0.22/0.53  tff(u83,negated_conjecture,
% 0.22/0.53      ((~~r1_yellow_0(sK1,sK2)) | ~r1_yellow_0(sK1,sK2))).
% 0.22/0.53  
% 0.22/0.53  tff(u82,axiom,
% 0.22/0.53      (![X1, X3, X0, X2] : ((~r1_yellow_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | r1_yellow_0(X1,X3))))).
% 0.22/0.53  
% 0.22/0.53  tff(u81,negated_conjecture,
% 0.22/0.53      r1_yellow_0(sK0,sK2)).
% 0.22/0.53  
% 0.22/0.53  tff(u80,axiom,
% 0.22/0.53      (![X1, X3, X0, X2] : ((~r2_hidden(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | r2_hidden(X1,X3))))).
% 0.22/0.53  
% 0.22/0.53  tff(u79,axiom,
% 0.22/0.53      (![X1, X3, X0, X2] : ((~v4_waybel_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | v4_waybel_0(X1,X3))))).
% 0.22/0.53  
% 0.22/0.53  tff(u78,axiom,
% 0.22/0.53      (![X1, X3, X0, X2] : ((~v1_waybel_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | v1_waybel_0(X1,X3))))).
% 0.22/0.53  
% 0.22/0.53  tff(u77,axiom,
% 0.22/0.53      (![X1, X0, X2] : ((~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X0,X2))))).
% 0.22/0.53  
% 0.22/0.53  tff(u76,axiom,
% 0.22/0.53      (![X1, X0] : ((~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X1,X0))))).
% 0.22/0.53  
% 0.22/0.53  tff(u75,negated_conjecture,
% 0.22/0.53      ~sQ3_eqProxy(k1_xboole_0,sK2)).
% 0.22/0.53  
% 0.22/0.53  tff(u74,negated_conjecture,
% 0.22/0.53      ((~~r1_yellow_0(sK1,sK2)) | ~sQ3_eqProxy(sK0,sK1))).
% 0.22/0.53  
% 0.22/0.53  tff(u73,negated_conjecture,
% 0.22/0.53      ((~~r1_yellow_0(sK1,sK2)) | ~sQ3_eqProxy(sK1,sK0))).
% 0.22/0.53  
% 0.22/0.53  tff(u72,negated_conjecture,
% 0.22/0.53      ~sQ3_eqProxy(sK2,k1_xboole_0)).
% 0.22/0.53  
% 0.22/0.53  tff(u71,axiom,
% 0.22/0.53      (![X0] : (sQ3_eqProxy(X0,X0)))).
% 0.22/0.53  
% 0.22/0.53  tff(u70,axiom,
% 0.22/0.53      (![X1, X0] : ((sQ3_eqProxy(u1_struct_0(X0),u1_struct_0(X1)) | ~sQ3_eqProxy(X0,X1))))).
% 0.22/0.53  
% 0.22/0.53  tff(u69,axiom,
% 0.22/0.53      (![X1, X0] : ((sQ3_eqProxy(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~sQ3_eqProxy(X0,X1))))).
% 0.22/0.53  
% 0.22/0.53  tff(u68,axiom,
% 0.22/0.53      (![X1, X3, X0, X2] : ((sQ3_eqProxy(k1_yellow_0(X0,X2),k1_yellow_0(X1,X3)) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1))))).
% 0.22/0.53  
% 0.22/0.53  % (7958)# SZS output end Saturation.
% 0.22/0.53  % (7958)------------------------------
% 0.22/0.53  % (7958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7958)Termination reason: Satisfiable
% 0.22/0.53  
% 0.22/0.53  % (7958)Memory used [KB]: 10618
% 0.22/0.53  % (7958)Time elapsed: 0.085 s
% 0.22/0.53  % (7958)------------------------------
% 0.22/0.53  % (7958)------------------------------
% 0.22/0.53  % (7962)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  % (7961)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  % (7962)Refutation not found, incomplete strategy% (7962)------------------------------
% 0.22/0.53  % (7962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7962)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7962)Memory used [KB]: 1535
% 0.22/0.53  % (7962)Time elapsed: 0.083 s
% 0.22/0.53  % (7962)------------------------------
% 0.22/0.53  % (7962)------------------------------
% 0.22/0.53  % (7947)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (7937)Success in time 0.166 s
%------------------------------------------------------------------------------
