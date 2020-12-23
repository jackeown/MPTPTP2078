%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:15 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :    1 (   1 expanded)
%              Number of leaves         :    1 (   1 expanded)
%              Depth                    :    0
%              Number of atoms          :    1 (   1 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    3 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u12,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:00:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.39  % (6282)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.40  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.40  % (6282)# SZS output start Saturation.
% 0.19/0.40  tff(u12,axiom,
% 0.19/0.40      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0))))).
% 0.19/0.40  
% 0.19/0.40  % (6282)# SZS output end Saturation.
% 0.19/0.40  % (6282)------------------------------
% 0.19/0.40  % (6282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.40  % (6282)Termination reason: Satisfiable
% 0.19/0.40  
% 0.19/0.40  % (6282)Memory used [KB]: 6012
% 0.19/0.40  % (6282)Time elapsed: 0.019 s
% 0.19/0.40  % (6282)------------------------------
% 0.19/0.40  % (6282)------------------------------
% 0.19/0.41  % (6275)Success in time 0.053 s
%------------------------------------------------------------------------------
