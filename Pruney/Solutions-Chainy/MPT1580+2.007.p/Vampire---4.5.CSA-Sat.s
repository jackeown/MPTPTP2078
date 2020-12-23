%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:22 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u56,negated_conjecture,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u55,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u54,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) )).

tff(u53,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u52,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u51,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

tff(u50,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u49,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u48,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u47,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u46,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) )).

tff(u45,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u44,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u43,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u42,negated_conjecture,(
    m1_yellow_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:53:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (8345)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.47  % (8348)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.48  % (8356)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.48  % (8353)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.48  % (8353)Refutation not found, incomplete strategy% (8353)------------------------------
% 0.22/0.48  % (8353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (8353)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (8353)Memory used [KB]: 9722
% 0.22/0.48  % (8353)Time elapsed: 0.072 s
% 0.22/0.48  % (8353)------------------------------
% 0.22/0.48  % (8353)------------------------------
% 0.22/0.49  % (8351)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.49  % (8350)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.49  % (8350)# SZS output start Saturation.
% 0.22/0.49  tff(u56,negated_conjecture,
% 0.22/0.49      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.49  
% 0.22/0.49  tff(u55,axiom,
% 0.22/0.49      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u54,axiom,
% 0.22/0.49      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u53,negated_conjecture,
% 0.22/0.49      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.22/0.49  
% 0.22/0.49  tff(u52,axiom,
% 0.22/0.49      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u51,negated_conjecture,
% 0.22/0.49      ((~v1_xboole_0(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK1)))).
% 0.22/0.49  
% 0.22/0.49  tff(u50,axiom,
% 0.22/0.49      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.22/0.49  
% 0.22/0.49  tff(u49,axiom,
% 0.22/0.49      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u48,negated_conjecture,
% 0.22/0.49      ~v2_struct_0(sK1)).
% 0.22/0.49  
% 0.22/0.49  tff(u47,negated_conjecture,
% 0.22/0.49      ~v2_struct_0(sK0)).
% 0.22/0.49  
% 0.22/0.49  tff(u46,negated_conjecture,
% 0.22/0.49      ((~v1_xboole_0(u1_struct_0(sK1))) | ~l1_struct_0(sK1))).
% 0.22/0.49  
% 0.22/0.49  tff(u45,negated_conjecture,
% 0.22/0.49      l1_struct_0(sK0)).
% 0.22/0.49  
% 0.22/0.49  tff(u44,axiom,
% 0.22/0.49      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u43,negated_conjecture,
% 0.22/0.49      l1_orders_2(sK0)).
% 0.22/0.49  
% 0.22/0.49  tff(u42,negated_conjecture,
% 0.22/0.49      m1_yellow_0(sK1,sK0)).
% 0.22/0.49  
% 0.22/0.49  % (8350)# SZS output end Saturation.
% 0.22/0.49  % (8350)------------------------------
% 0.22/0.49  % (8350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8350)Termination reason: Satisfiable
% 0.22/0.49  
% 0.22/0.49  % (8350)Memory used [KB]: 5245
% 0.22/0.49  % (8350)Time elapsed: 0.002 s
% 0.22/0.49  % (8350)------------------------------
% 0.22/0.49  % (8350)------------------------------
% 0.22/0.49  % (8343)Success in time 0.13 s
%------------------------------------------------------------------------------
