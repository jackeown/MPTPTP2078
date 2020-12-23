%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:03 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u56,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK2(X0,X1),X2)
      | r1_tarski(X0,X1) ) )).

tff(u55,negated_conjecture,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ! [X3,X2] :
        ( ~ r1_tarski(sK1,X3)
        | r2_hidden(sK2(k3_waybel_0(sK0,sK1),X2),X3)
        | r1_tarski(k3_waybel_0(sK0,sK1),X2) ) )).

tff(u54,negated_conjecture,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | r1_tarski(k3_waybel_0(sK0,sK1),sK1) )).

tff(u53,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u52,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u51,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u50,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u49,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u48,negated_conjecture,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ! [X0] :
        ( r2_hidden(sK2(k3_waybel_0(sK0,sK1),X0),sK1)
        | r1_tarski(k3_waybel_0(sK0,sK1),X0) ) )).

tff(u47,negated_conjecture,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
        | r1_tarski(k3_waybel_0(sK0,sK1),X0)
        | m1_subset_1(sK2(k3_waybel_0(sK0,sK1),X0),X1) ) )).

tff(u46,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK2(X0,X2),X1)
      | r1_tarski(X0,X2) ) )).

tff(u45,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u44,negated_conjecture,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ! [X0] :
        ( m1_subset_1(sK2(k3_waybel_0(sK0,sK1),X0),u1_struct_0(sK0))
        | r1_tarski(k3_waybel_0(sK0,sK1),X0) ) )).

tff(u43,negated_conjecture,(
    ! [X0] :
      ( m1_subset_1(sK2(sK1,X0),u1_struct_0(sK0))
      | r1_tarski(sK1,X0) ) )).

tff(u42,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u41,negated_conjecture,
    ( ~ ~ v12_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.43  % (24952)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.44  % (24945)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.45  % (24962)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (24947)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.47  % (24950)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.47  % (24947)Refutation not found, incomplete strategy% (24947)------------------------------
% 0.20/0.47  % (24947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (24947)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (24947)Memory used [KB]: 9850
% 0.20/0.47  % (24947)Time elapsed: 0.076 s
% 0.20/0.47  % (24947)------------------------------
% 0.20/0.47  % (24947)------------------------------
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (24950)# SZS output start Saturation.
% 0.20/0.47  tff(u56,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK2(X0,X1),X2) | r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u55,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k3_waybel_0(sK0,sK1),sK1)) | (![X3, X2] : ((~r1_tarski(sK1,X3) | r2_hidden(sK2(k3_waybel_0(sK0,sK1),X2),X3) | r1_tarski(k3_waybel_0(sK0,sK1),X2)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u54,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k3_waybel_0(sK0,sK1),sK1)) | r1_tarski(k3_waybel_0(sK0,sK1),sK1))).
% 0.20/0.47  
% 0.20/0.47  tff(u53,axiom,
% 0.20/0.47      (![X0] : (r1_tarski(X0,X0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u52,axiom,
% 0.20/0.47      (![X1, X0] : ((~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u51,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u50,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u49,axiom,
% 0.20/0.47      (![X1, X0] : ((r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u48,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k3_waybel_0(sK0,sK1),sK1)) | (![X0] : ((r2_hidden(sK2(k3_waybel_0(sK0,sK1),X0),sK1) | r1_tarski(k3_waybel_0(sK0,sK1),X0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u47,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k3_waybel_0(sK0,sK1),sK1)) | (![X1, X0] : ((~m1_subset_1(sK1,k1_zfmisc_1(X1)) | r1_tarski(k3_waybel_0(sK0,sK1),X0) | m1_subset_1(sK2(k3_waybel_0(sK0,sK1),X0),X1)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u46,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK2(X0,X2),X1) | r1_tarski(X0,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u45,negated_conjecture,
% 0.20/0.47      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u44,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k3_waybel_0(sK0,sK1),sK1)) | (![X0] : ((m1_subset_1(sK2(k3_waybel_0(sK0,sK1),X0),u1_struct_0(sK0)) | r1_tarski(k3_waybel_0(sK0,sK1),X0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u43,negated_conjecture,
% 0.20/0.47      (![X0] : ((m1_subset_1(sK2(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u42,negated_conjecture,
% 0.20/0.47      l1_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u41,negated_conjecture,
% 0.20/0.47      ((~~v12_waybel_0(sK1,sK0)) | ~v12_waybel_0(sK1,sK0))).
% 0.20/0.47  
% 0.20/0.47  % (24950)# SZS output end Saturation.
% 0.20/0.47  % (24950)------------------------------
% 0.20/0.47  % (24950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (24950)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (24950)Memory used [KB]: 5373
% 0.20/0.47  % (24950)Time elapsed: 0.004 s
% 0.20/0.47  % (24950)------------------------------
% 0.20/0.47  % (24950)------------------------------
% 0.20/0.47  % (24964)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.48  % (24943)Success in time 0.126 s
%------------------------------------------------------------------------------
