%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
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
    ( ~ ~ r2_yellow_0(sK1,sK2)
    | ~ r2_yellow_0(sK1,sK2) )).

tff(u82,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_yellow_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | r2_yellow_0(X1,X3) ) )).

tff(u81,negated_conjecture,(
    r2_yellow_0(sK0,sK2) )).

tff(u80,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | r2_hidden(X1,X3) ) )).

tff(u79,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ v3_waybel_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | v3_waybel_0(X1,X3) ) )).

tff(u78,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ v2_waybel_0(X0,X2)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1)
      | v2_waybel_0(X1,X3) ) )).

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
    ( ~ ~ r2_yellow_0(sK1,sK2)
    | ~ sQ3_eqProxy(sK0,sK1) )).

tff(u73,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK1,sK2)
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
      ( sQ3_eqProxy(k2_yellow_0(X0,X2),k2_yellow_0(X1,X3))
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.46  % (16385)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.46  % (16395)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.46  % (16395)Refutation not found, incomplete strategy% (16395)------------------------------
% 0.22/0.46  % (16395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (16385)Refutation not found, incomplete strategy% (16385)------------------------------
% 0.22/0.47  % (16385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (16385)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (16385)Memory used [KB]: 6012
% 0.22/0.47  % (16385)Time elapsed: 0.054 s
% 0.22/0.47  % (16385)------------------------------
% 0.22/0.47  % (16385)------------------------------
% 0.22/0.47  % (16394)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  % (16395)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (16395)Memory used [KB]: 10618
% 0.22/0.47  % (16395)Time elapsed: 0.057 s
% 0.22/0.47  % (16395)------------------------------
% 0.22/0.47  % (16395)------------------------------
% 0.22/0.47  % (16389)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (16401)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (16401)Refutation not found, incomplete strategy% (16401)------------------------------
% 0.22/0.48  % (16401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16401)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (16401)Memory used [KB]: 6012
% 0.22/0.48  % (16401)Time elapsed: 0.002 s
% 0.22/0.48  % (16401)------------------------------
% 0.22/0.48  % (16401)------------------------------
% 0.22/0.48  % (16389)Refutation not found, incomplete strategy% (16389)------------------------------
% 0.22/0.48  % (16389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16389)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (16389)Memory used [KB]: 1663
% 0.22/0.48  % (16389)Time elapsed: 0.068 s
% 0.22/0.48  % (16389)------------------------------
% 0.22/0.48  % (16389)------------------------------
% 0.22/0.48  % (16406)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (16390)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (16400)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (16400)# SZS output start Saturation.
% 0.22/0.48  tff(u89,axiom,
% 0.22/0.48      (![X1, X0] : ((~v2_struct_0(X0) | ~sQ3_eqProxy(X0,X1) | v2_struct_0(X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u88,axiom,
% 0.22/0.48      (![X1, X0] : ((~v4_orders_2(X0) | ~sQ3_eqProxy(X0,X1) | v4_orders_2(X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u87,axiom,
% 0.22/0.48      (![X1, X0] : ((~l1_orders_2(X0) | ~sQ3_eqProxy(X0,X1) | l1_orders_2(X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u86,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((~v4_yellow_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | v4_yellow_0(X1,X3))))).
% 0.22/0.48  
% 0.22/0.48  tff(u85,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((~m1_yellow_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | m1_yellow_0(X1,X3))))).
% 0.22/0.48  
% 0.22/0.48  tff(u84,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((~m1_subset_1(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | m1_subset_1(X1,X3))))).
% 0.22/0.48  
% 0.22/0.48  tff(u83,negated_conjecture,
% 0.22/0.48      ((~~r2_yellow_0(sK1,sK2)) | ~r2_yellow_0(sK1,sK2))).
% 0.22/0.48  
% 0.22/0.48  tff(u82,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((~r2_yellow_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | r2_yellow_0(X1,X3))))).
% 0.22/0.48  
% 0.22/0.48  tff(u81,negated_conjecture,
% 0.22/0.48      r2_yellow_0(sK0,sK2)).
% 0.22/0.48  
% 0.22/0.48  tff(u80,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((~r2_hidden(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | r2_hidden(X1,X3))))).
% 0.22/0.48  
% 0.22/0.48  tff(u79,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((~v3_waybel_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | v3_waybel_0(X1,X3))))).
% 0.22/0.48  
% 0.22/0.48  tff(u78,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((~v2_waybel_0(X0,X2) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1) | v2_waybel_0(X1,X3))))).
% 0.22/0.48  
% 0.22/0.48  tff(u77,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X0,X2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u76,axiom,
% 0.22/0.48      (![X1, X0] : ((~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X1,X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u75,negated_conjecture,
% 0.22/0.48      ~sQ3_eqProxy(k1_xboole_0,sK2)).
% 0.22/0.48  
% 0.22/0.48  tff(u74,negated_conjecture,
% 0.22/0.48      ((~~r2_yellow_0(sK1,sK2)) | ~sQ3_eqProxy(sK0,sK1))).
% 0.22/0.48  
% 0.22/0.48  tff(u73,negated_conjecture,
% 0.22/0.48      ((~~r2_yellow_0(sK1,sK2)) | ~sQ3_eqProxy(sK1,sK0))).
% 0.22/0.48  
% 0.22/0.48  tff(u72,negated_conjecture,
% 0.22/0.48      ~sQ3_eqProxy(sK2,k1_xboole_0)).
% 0.22/0.48  
% 0.22/0.48  tff(u71,axiom,
% 0.22/0.48      (![X0] : (sQ3_eqProxy(X0,X0)))).
% 0.22/0.48  
% 0.22/0.48  tff(u70,axiom,
% 0.22/0.48      (![X1, X0] : ((sQ3_eqProxy(u1_struct_0(X0),u1_struct_0(X1)) | ~sQ3_eqProxy(X0,X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u69,axiom,
% 0.22/0.48      (![X1, X0] : ((sQ3_eqProxy(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~sQ3_eqProxy(X0,X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u68,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((sQ3_eqProxy(k2_yellow_0(X0,X2),k2_yellow_0(X1,X3)) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X0,X1))))).
% 0.22/0.48  
% 0.22/0.48  % (16400)# SZS output end Saturation.
% 0.22/0.48  % (16400)------------------------------
% 0.22/0.48  % (16400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16400)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (16400)Memory used [KB]: 10618
% 0.22/0.48  % (16400)Time elapsed: 0.084 s
% 0.22/0.48  % (16400)------------------------------
% 0.22/0.48  % (16400)------------------------------
% 0.22/0.49  % (16381)Success in time 0.128 s
%------------------------------------------------------------------------------
