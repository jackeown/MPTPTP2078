%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
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
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u12,negated_conjecture,(
    k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (3127)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (3127)# SZS output start Saturation.
% 0.21/0.47  tff(u12,negated_conjecture,
% 0.21/0.47      (k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))))).
% 0.21/0.47  
% 0.21/0.47  % (3127)# SZS output end Saturation.
% 0.21/0.47  % (3127)------------------------------
% 0.21/0.47  % (3127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3127)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (3127)Memory used [KB]: 10618
% 0.21/0.47  % (3127)Time elapsed: 0.050 s
% 0.21/0.47  % (3127)------------------------------
% 0.21/0.47  % (3127)------------------------------
% 0.21/0.47  % (3123)Success in time 0.111 s
%------------------------------------------------------------------------------
