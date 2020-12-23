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
% DateTime   : Thu Dec  3 13:16:19 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    1 (   1 expanded)
%              Number of leaves         :    1 (   1 expanded)
%              Depth                    :    0
%              Number of atoms          :    1 (   1 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    2 (   2 average)
%              Maximal term depth       :    5 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u13,negated_conjecture,(
    k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:24:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (14967)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (14965)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (14965)# SZS output start Saturation.
% 0.21/0.46  tff(u13,negated_conjecture,
% 0.21/0.46      (k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))))).
% 0.21/0.46  
% 0.21/0.46  % (14965)# SZS output end Saturation.
% 0.21/0.46  % (14965)------------------------------
% 0.21/0.46  % (14965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (14965)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (14965)Memory used [KB]: 6012
% 0.21/0.46  % (14965)Time elapsed: 0.044 s
% 0.21/0.46  % (14965)------------------------------
% 0.21/0.46  % (14965)------------------------------
% 0.21/0.47  % (14960)Success in time 0.106 s
%------------------------------------------------------------------------------
