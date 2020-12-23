%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:08 EST 2020

% Result     : CounterSatisfiable 1.43s
% Output     : Saturation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   42 (  42 expanded)
%              Number of leaves         :   42 (  42 expanded)
%              Depth                    :    0
%              Number of atoms          :  152 ( 152 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u197,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK6(X0,X1),X2)
      | r1_tarski(X0,X1) ) )).

tff(u196,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u195,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X0) ) )).

tff(u194,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X0) ) )).

tff(u193,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X0) ) )).

tff(u192,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | m1_pre_topc(X1,X0) ) )).

tff(u191,negated_conjecture,
    ( ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | ! [X1,X0] :
        ( ~ r1_tarski(k2_struct_0(sK0),X1)
        | r2_hidden(sK6(k2_struct_0(sK1),X0),X1)
        | r1_tarski(k2_struct_0(sK1),X0) ) )).

tff(u190,negated_conjecture,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | ! [X1,X0] :
        ( ~ r1_tarski(u1_struct_0(sK1),X1)
        | r2_hidden(sK6(sK2,X0),X1)
        | r1_tarski(sK2,X0) ) )).

tff(u189,negated_conjecture,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | r1_tarski(sK2,u1_struct_0(sK1)) )).

tff(u188,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u187,negated_conjecture,
    ( ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)) )).

tff(u186,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u185,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u184,negated_conjecture,
    ( ~ ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ r2_hidden(sK2,u1_pre_topc(sK1)) )).

tff(u183,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | k9_subset_1(u1_struct_0(X1),u1_struct_0(X2),k2_struct_0(X1)) != sK3(X2,X1)
      | ~ r2_hidden(sK3(X2,X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X2) ) )).

tff(u182,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X2)
      | u1_struct_0(X1) = k9_subset_1(u1_struct_0(X1),sK4(X2,X1,u1_struct_0(X1)),k2_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X2) ) )).

tff(u181,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X2)
      | m1_subset_1(sK4(X2,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X2) ) )).

tff(u180,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X2)
      | r2_hidden(sK4(X2,X1,u1_struct_0(X1)),u1_pre_topc(X2))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X2) ) )).

tff(u179,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u178,negated_conjecture,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | ! [X0] :
        ( r2_hidden(sK6(sK2,X0),u1_struct_0(sK1))
        | r1_tarski(sK2,X0) ) )).

tff(u177,negated_conjecture,
    ( ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | ! [X3] :
        ( r2_hidden(sK6(k2_struct_0(sK1),X3),k2_struct_0(sK0))
        | r1_tarski(k2_struct_0(sK1),X3) ) )).

tff(u176,negated_conjecture,
    ( ~ ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u175,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u174,axiom,(
    ! [X1,X3,X0] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X0) ) )).

tff(u173,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
      | ~ r2_hidden(X2,u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0) ) )).

tff(u172,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0) ) )).

tff(u171,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0) ) )).

tff(u170,axiom,(
    ! [X1,X3,X0] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | r2_hidden(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0) ) )).

tff(u169,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u168,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u167,negated_conjecture,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0))) )).

tff(u166,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | sK3(X0,X0) = k9_subset_1(u1_struct_0(X0),sK5(X0,X0),k2_struct_0(X0))
      | r2_hidden(sK3(X0,X0),u1_pre_topc(X0))
      | m1_pre_topc(X0,X0) ) )).

tff(u165,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK5(X0,X0),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK3(X0,X0),u1_pre_topc(X0))
      | m1_pre_topc(X0,X0) ) )).

tff(u164,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK5(X0,X0),u1_pre_topc(X0))
      | r2_hidden(sK3(X0,X0),u1_pre_topc(X0))
      | m1_pre_topc(X0,X0) ) )).

tff(u163,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X0),k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(X0,X0) ) )).

tff(u162,negated_conjecture,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK0) )).

tff(u161,negated_conjecture,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK1) )).

tff(u160,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) )).

tff(u159,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) )).

tff(u158,negated_conjecture,
    ( ~ m1_pre_topc(sK1,sK0)
    | m1_pre_topc(sK1,sK0) )).

tff(u157,negated_conjecture,
    ( ~ m1_pre_topc(sK0,sK0)
    | m1_pre_topc(sK0,sK0) )).

tff(u156,negated_conjecture,
    ( ~ m1_pre_topc(sK1,sK1)
    | m1_pre_topc(sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:46:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.48  % (32455)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (32439)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.49  % (32442)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (32442)Refutation not found, incomplete strategy% (32442)------------------------------
% 0.21/0.49  % (32442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32442)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32442)Memory used [KB]: 10746
% 0.21/0.49  % (32442)Time elapsed: 0.088 s
% 0.21/0.49  % (32442)------------------------------
% 0.21/0.49  % (32442)------------------------------
% 0.21/0.49  % (32452)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % (32463)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.49  % (32452)Refutation not found, incomplete strategy% (32452)------------------------------
% 0.21/0.49  % (32452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32452)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32452)Memory used [KB]: 10618
% 0.21/0.49  % (32452)Time elapsed: 0.099 s
% 0.21/0.49  % (32452)------------------------------
% 0.21/0.49  % (32452)------------------------------
% 0.21/0.50  % (32449)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (32437)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (32457)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (32458)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (32446)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (32438)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (32446)Refutation not found, incomplete strategy% (32446)------------------------------
% 0.21/0.51  % (32446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32446)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32446)Memory used [KB]: 10618
% 0.21/0.51  % (32446)Time elapsed: 0.109 s
% 0.21/0.51  % (32446)------------------------------
% 0.21/0.51  % (32446)------------------------------
% 0.21/0.51  % (32457)Refutation not found, incomplete strategy% (32457)------------------------------
% 0.21/0.51  % (32457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32438)Refutation not found, incomplete strategy% (32438)------------------------------
% 0.21/0.51  % (32438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32440)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (32457)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32457)Memory used [KB]: 10746
% 0.21/0.51  % (32457)Time elapsed: 0.115 s
% 0.21/0.51  % (32457)------------------------------
% 0.21/0.51  % (32457)------------------------------
% 1.26/0.52  % (32441)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.26/0.52  % (32436)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.52  % (32436)Refutation not found, incomplete strategy% (32436)------------------------------
% 1.26/0.52  % (32436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (32462)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.26/0.52  % (32461)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.26/0.52  % (32464)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.26/0.52  % (32459)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.26/0.52  % (32456)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.26/0.52  % (32447)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.52  % (32448)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.26/0.53  % (32436)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (32436)Memory used [KB]: 10746
% 1.26/0.53  % (32436)Time elapsed: 0.119 s
% 1.26/0.53  % (32436)------------------------------
% 1.26/0.53  % (32436)------------------------------
% 1.26/0.53  % (32435)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.53  % (32456)Refutation not found, incomplete strategy% (32456)------------------------------
% 1.26/0.53  % (32456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (32456)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (32456)Memory used [KB]: 1791
% 1.26/0.53  % (32456)Time elapsed: 0.137 s
% 1.26/0.53  % (32456)------------------------------
% 1.26/0.53  % (32456)------------------------------
% 1.26/0.53  % (32443)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.26/0.53  % (32450)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.53  % (32443)Refutation not found, incomplete strategy% (32443)------------------------------
% 1.26/0.53  % (32443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (32443)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (32443)Memory used [KB]: 10618
% 1.26/0.53  % (32443)Time elapsed: 0.102 s
% 1.26/0.53  % (32443)------------------------------
% 1.26/0.53  % (32443)------------------------------
% 1.26/0.53  % (32454)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.26/0.53  % (32434)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.53  % (32461)Refutation not found, incomplete strategy% (32461)------------------------------
% 1.26/0.53  % (32461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (32461)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (32461)Memory used [KB]: 10746
% 1.26/0.53  % (32461)Time elapsed: 0.149 s
% 1.26/0.53  % (32461)------------------------------
% 1.26/0.53  % (32461)------------------------------
% 1.26/0.53  % (32434)Refutation not found, incomplete strategy% (32434)------------------------------
% 1.26/0.53  % (32434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (32434)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (32434)Memory used [KB]: 1663
% 1.26/0.53  % (32434)Time elapsed: 0.137 s
% 1.26/0.53  % (32434)------------------------------
% 1.26/0.53  % (32434)------------------------------
% 1.26/0.54  % (32453)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.54  % (32438)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (32438)Memory used [KB]: 6268
% 1.43/0.54  % (32438)Time elapsed: 0.110 s
% 1.43/0.54  % (32438)------------------------------
% 1.43/0.54  % (32438)------------------------------
% 1.43/0.54  % (32445)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.54  % (32445)Refutation not found, incomplete strategy% (32445)------------------------------
% 1.43/0.54  % (32445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (32445)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (32445)Memory used [KB]: 10618
% 1.43/0.54  % (32445)Time elapsed: 0.138 s
% 1.43/0.54  % (32445)------------------------------
% 1.43/0.54  % (32445)------------------------------
% 1.43/0.54  % (32451)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.43/0.55  % (32451)# SZS output start Saturation.
% 1.43/0.55  tff(u197,axiom,
% 1.43/0.55      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK6(X0,X1),X2) | r1_tarski(X0,X1))))).
% 1.43/0.55  
% 1.43/0.55  tff(u196,axiom,
% 1.43/0.55      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 1.43/0.55  
% 1.43/0.55  tff(u195,axiom,
% 1.43/0.55      (![X1, X0] : ((~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | (sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u194,axiom,
% 1.43/0.55      (![X1, X0] : ((~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u193,axiom,
% 1.43/0.55      (![X1, X0] : ((~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u192,axiom,
% 1.43/0.55      (![X1, X0] : ((~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | m1_pre_topc(X1,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u191,negated_conjecture,
% 1.43/0.55      ((~r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))) | (![X1, X0] : ((~r1_tarski(k2_struct_0(sK0),X1) | r2_hidden(sK6(k2_struct_0(sK1),X0),X1) | r1_tarski(k2_struct_0(sK1),X0)))))).
% 1.43/0.55  
% 1.43/0.55  tff(u190,negated_conjecture,
% 1.43/0.55      ((~r1_tarski(sK2,u1_struct_0(sK1))) | (![X1, X0] : ((~r1_tarski(u1_struct_0(sK1),X1) | r2_hidden(sK6(sK2,X0),X1) | r1_tarski(sK2,X0)))))).
% 1.43/0.55  
% 1.43/0.55  tff(u189,negated_conjecture,
% 1.43/0.55      ((~r1_tarski(sK2,u1_struct_0(sK1))) | r1_tarski(sK2,u1_struct_0(sK1)))).
% 1.43/0.55  
% 1.43/0.55  tff(u188,axiom,
% 1.43/0.55      (![X0] : (r1_tarski(X0,X0)))).
% 1.43/0.55  
% 1.43/0.55  tff(u187,negated_conjecture,
% 1.43/0.55      ((~r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))) | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)))).
% 1.43/0.55  
% 1.43/0.55  tff(u186,axiom,
% 1.43/0.55      (![X1, X0] : ((~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1))))).
% 1.43/0.55  
% 1.43/0.55  tff(u185,axiom,
% 1.43/0.55      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 1.43/0.55  
% 1.43/0.55  tff(u184,negated_conjecture,
% 1.43/0.55      ((~~r2_hidden(sK2,u1_pre_topc(sK1))) | ~r2_hidden(sK2,u1_pre_topc(sK1)))).
% 1.43/0.55  
% 1.43/0.55  tff(u183,axiom,
% 1.43/0.55      (![X1, X2] : ((~r2_hidden(u1_struct_0(X2),u1_pre_topc(X2)) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X2)) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | (k9_subset_1(u1_struct_0(X1),u1_struct_0(X2),k2_struct_0(X1)) != sK3(X2,X1)) | ~r2_hidden(sK3(X2,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X2))))).
% 1.43/0.55  
% 1.43/0.55  tff(u182,axiom,
% 1.43/0.55      (![X1, X2] : ((~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X2) | (u1_struct_0(X1) = k9_subset_1(u1_struct_0(X1),sK4(X2,X1,u1_struct_0(X1)),k2_struct_0(X1))) | ~l1_pre_topc(X1) | ~m1_pre_topc(X1,X2))))).
% 1.43/0.55  
% 1.43/0.55  tff(u181,axiom,
% 1.43/0.55      (![X1, X2] : ((~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X2) | m1_subset_1(sK4(X2,X1,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X1) | ~m1_pre_topc(X1,X2))))).
% 1.43/0.55  
% 1.43/0.55  tff(u180,axiom,
% 1.43/0.55      (![X1, X2] : ((~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X2) | r2_hidden(sK4(X2,X1,u1_struct_0(X1)),u1_pre_topc(X2)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X1,X2))))).
% 1.43/0.55  
% 1.43/0.55  tff(u179,axiom,
% 1.43/0.55      (![X1, X0] : ((r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1))))).
% 1.43/0.55  
% 1.43/0.55  tff(u178,negated_conjecture,
% 1.43/0.55      ((~r1_tarski(sK2,u1_struct_0(sK1))) | (![X0] : ((r2_hidden(sK6(sK2,X0),u1_struct_0(sK1)) | r1_tarski(sK2,X0)))))).
% 1.43/0.55  
% 1.43/0.55  tff(u177,negated_conjecture,
% 1.43/0.55      ((~r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))) | (![X3] : ((r2_hidden(sK6(k2_struct_0(sK1),X3),k2_struct_0(sK0)) | r1_tarski(k2_struct_0(sK1),X3)))))).
% 1.43/0.55  
% 1.43/0.55  tff(u176,negated_conjecture,
% 1.43/0.55      ((~~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u175,axiom,
% 1.43/0.55      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 1.43/0.55  
% 1.43/0.55  tff(u174,axiom,
% 1.43/0.55      (![X1, X3, X0] : ((~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~r2_hidden(X3,u1_pre_topc(X0)) | (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u173,axiom,
% 1.43/0.55      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | (k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2) | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u172,axiom,
% 1.43/0.55      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u171,axiom,
% 1.43/0.55      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u170,axiom,
% 1.43/0.55      (![X1, X3, X0] : ((~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,u1_pre_topc(X0)) | r2_hidden(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u169,negated_conjecture,
% 1.43/0.55      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))).
% 1.43/0.55  
% 1.43/0.55  tff(u168,axiom,
% 1.43/0.55      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u167,negated_conjecture,
% 1.43/0.55      ((~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0)))) | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u166,axiom,
% 1.43/0.55      (![X0] : ((~l1_pre_topc(X0) | (sK3(X0,X0) = k9_subset_1(u1_struct_0(X0),sK5(X0,X0),k2_struct_0(X0))) | r2_hidden(sK3(X0,X0),u1_pre_topc(X0)) | m1_pre_topc(X0,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u165,axiom,
% 1.43/0.55      (![X0] : ((~l1_pre_topc(X0) | m1_subset_1(sK5(X0,X0),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK3(X0,X0),u1_pre_topc(X0)) | m1_pre_topc(X0,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u164,axiom,
% 1.43/0.55      (![X0] : ((~l1_pre_topc(X0) | r2_hidden(sK5(X0,X0),u1_pre_topc(X0)) | r2_hidden(sK3(X0,X0),u1_pre_topc(X0)) | m1_pre_topc(X0,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u163,axiom,
% 1.43/0.55      (![X0] : ((~l1_pre_topc(X0) | m1_subset_1(sK3(X0,X0),k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(X0,X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u162,negated_conjecture,
% 1.43/0.55      ((~l1_pre_topc(sK0)) | l1_pre_topc(sK0))).
% 1.43/0.55  
% 1.43/0.55  tff(u161,negated_conjecture,
% 1.43/0.55      ((~l1_pre_topc(sK1)) | l1_pre_topc(sK1))).
% 1.43/0.55  
% 1.43/0.55  tff(u160,axiom,
% 1.43/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0))))).
% 1.43/0.55  
% 1.43/0.55  tff(u159,axiom,
% 1.43/0.55      (![X1, X0] : ((~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1))))).
% 1.43/0.55  
% 1.43/0.55  tff(u158,negated_conjecture,
% 1.43/0.55      ((~m1_pre_topc(sK1,sK0)) | m1_pre_topc(sK1,sK0))).
% 1.43/0.55  
% 1.43/0.55  tff(u157,negated_conjecture,
% 1.43/0.55      ((~m1_pre_topc(sK0,sK0)) | m1_pre_topc(sK0,sK0))).
% 1.43/0.55  
% 1.43/0.55  tff(u156,negated_conjecture,
% 1.43/0.55      ((~m1_pre_topc(sK1,sK1)) | m1_pre_topc(sK1,sK1))).
% 1.43/0.55  
% 1.43/0.55  % (32451)# SZS output end Saturation.
% 1.43/0.55  % (32451)------------------------------
% 1.43/0.55  % (32451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (32451)Termination reason: Satisfiable
% 1.43/0.55  
% 1.43/0.55  % (32451)Memory used [KB]: 10746
% 1.43/0.55  % (32451)Time elapsed: 0.151 s
% 1.43/0.55  % (32451)------------------------------
% 1.43/0.55  % (32451)------------------------------
% 1.43/0.55  % (32431)Success in time 0.187 s
%------------------------------------------------------------------------------
