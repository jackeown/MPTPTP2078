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
% DateTime   : Thu Dec  3 13:09:03 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u47,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) )
    | k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) )).

tff(u46,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u45,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u44,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

tff(u43,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) )).

tff(u42,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u41,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u40,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (31468)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (31473)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (31474)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (31484)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (31474)# SZS output start Saturation.
% 0.21/0.51  tff(u47,negated_conjecture,
% 0.21/0.51      ((~(k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)))) | (k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u46,axiom,
% 0.21/0.51      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u45,axiom,
% 0.21/0.51      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.51  
% 0.21/0.51  tff(u44,axiom,
% 0.21/0.51      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 0.21/0.51  
% 0.21/0.51  tff(u43,axiom,
% 0.21/0.51      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u42,axiom,
% 0.21/0.51      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u41,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u40,negated_conjecture,
% 0.21/0.51      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  % (31474)# SZS output end Saturation.
% 0.21/0.51  % (31474)------------------------------
% 0.21/0.51  % (31474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31474)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (31474)Memory used [KB]: 6012
% 0.21/0.51  % (31474)Time elapsed: 0.073 s
% 0.21/0.51  % (31474)------------------------------
% 0.21/0.51  % (31474)------------------------------
% 0.21/0.51  % (31467)Success in time 0.149 s
%------------------------------------------------------------------------------
