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
% DateTime   : Thu Dec  3 13:17:04 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   49 (  49 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u92,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) )).

tff(u91,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK2(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) )).

tff(u90,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) )).

tff(u89,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u88,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2(u1_struct_0(sK0),sK1,X0),sK1)
      | r1_tarski(sK1,X0) ) )).

tff(u87,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))
      | r1_tarski(sK1,X0) ) )).

tff(u86,negated_conjecture,
    ( ~ r1_tarski(sK1,sK1)
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | m1_subset_1(sK2(sK1,sK1,X1),sK1)
        | r1_tarski(sK1,X1) ) )).

tff(u85,negated_conjecture,
    ( ~ r1_tarski(sK1,sK1)
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | r2_hidden(sK2(sK1,sK1,X0),sK1)
        | r1_tarski(sK1,X0) ) )).

tff(u84,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u83,negated_conjecture,
    ( ~ r1_tarski(sK1,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(sK1)) )).

tff(u82,negated_conjecture,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,u1_struct_0(sK0)) ) )).

tff(u81,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u80,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) )).

tff(u79,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u78,negated_conjecture,
    ( ~ ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1) )).

tff(u77,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u76,negated_conjecture,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,sK1) )).

tff(u75,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u74,negated_conjecture,
    ( ~ v12_waybel_0(sK1,sK0)
    | v12_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:13:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (10995)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.45  % (10988)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.47  % (10995)Refutation not found, incomplete strategy% (10995)------------------------------
% 0.22/0.47  % (10995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (10995)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (10995)Memory used [KB]: 9850
% 0.22/0.47  % (10995)Time elapsed: 0.057 s
% 0.22/0.47  % (10995)------------------------------
% 0.22/0.47  % (10995)------------------------------
% 0.22/0.48  % (11000)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.48  % (10994)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (11000)Refutation not found, incomplete strategy% (11000)------------------------------
% 0.22/0.48  % (11000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (11000)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (11000)Memory used [KB]: 5373
% 0.22/0.48  % (11000)Time elapsed: 0.004 s
% 0.22/0.48  % (11000)------------------------------
% 0.22/0.48  % (11000)------------------------------
% 0.22/0.48  % (10999)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.48  % (10991)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.48  % (10991)Refutation not found, incomplete strategy% (10991)------------------------------
% 0.22/0.48  % (10991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10992)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.49  % (10992)# SZS output start Saturation.
% 0.22/0.49  tff(u92,axiom,
% 0.22/0.49      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK2(X0,X1,X2),X1) | r1_tarski(X1,X2))))).
% 0.22/0.49  
% 0.22/0.49  tff(u91,axiom,
% 0.22/0.49      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK2(X0,X1,X2),X0) | r1_tarski(X1,X2))))).
% 0.22/0.49  
% 0.22/0.49  tff(u90,axiom,
% 0.22/0.49      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u89,axiom,
% 0.22/0.49      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u88,negated_conjecture,
% 0.22/0.49      (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(u1_struct_0(sK0),sK1,X0),sK1) | r1_tarski(sK1,X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u87,negated_conjecture,
% 0.22/0.49      (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u86,negated_conjecture,
% 0.22/0.49      ((~r1_tarski(sK1,sK1)) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(sK1)) | m1_subset_1(sK2(sK1,sK1,X1),sK1) | r1_tarski(sK1,X1)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u85,negated_conjecture,
% 0.22/0.49      ((~r1_tarski(sK1,sK1)) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(sK1)) | r2_hidden(sK2(sK1,sK1,X0),sK1) | r1_tarski(sK1,X0)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u84,negated_conjecture,
% 0.22/0.49      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.49  
% 0.22/0.49  tff(u83,negated_conjecture,
% 0.22/0.49      ((~r1_tarski(sK1,sK1)) | m1_subset_1(sK1,k1_zfmisc_1(sK1)))).
% 0.22/0.49  
% 0.22/0.49  tff(u82,negated_conjecture,
% 0.22/0.49      (![X0] : ((~r2_hidden(X0,sK1) | r2_hidden(X0,u1_struct_0(sK0)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u81,axiom,
% 0.22/0.49      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.22/0.49  
% 0.22/0.49  tff(u80,axiom,
% 0.22/0.49      (![X1, X0, X2] : ((~r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2))))).
% 0.22/0.49  
% 0.22/0.49  tff(u79,axiom,
% 0.22/0.49      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u78,negated_conjecture,
% 0.22/0.49      ((~~r1_tarski(k3_waybel_0(sK0,sK1),sK1)) | ~r1_tarski(k3_waybel_0(sK0,sK1),sK1))).
% 0.22/0.49  
% 0.22/0.49  tff(u77,negated_conjecture,
% 0.22/0.49      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.22/0.49  
% 0.22/0.49  tff(u76,negated_conjecture,
% 0.22/0.49      ((~r1_tarski(sK1,sK1)) | r1_tarski(sK1,sK1))).
% 0.22/0.49  
% 0.22/0.49  tff(u75,negated_conjecture,
% 0.22/0.49      l1_orders_2(sK0)).
% 0.22/0.49  
% 0.22/0.49  tff(u74,negated_conjecture,
% 0.22/0.49      ((~v12_waybel_0(sK1,sK0)) | v12_waybel_0(sK1,sK0))).
% 0.22/0.49  
% 0.22/0.49  % (10992)# SZS output end Saturation.
% 0.22/0.49  % (10992)------------------------------
% 0.22/0.49  % (10992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10992)Termination reason: Satisfiable
% 0.22/0.49  
% 0.22/0.49  % (10992)Memory used [KB]: 5373
% 0.22/0.49  % (10992)Time elapsed: 0.007 s
% 0.22/0.49  % (10992)------------------------------
% 0.22/0.49  % (10992)------------------------------
% 0.22/0.49  % (10987)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.49  % (10985)Success in time 0.129 s
%------------------------------------------------------------------------------
