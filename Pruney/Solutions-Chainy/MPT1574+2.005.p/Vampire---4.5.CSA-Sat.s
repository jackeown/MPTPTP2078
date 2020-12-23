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
% DateTime   : Thu Dec  3 13:16:20 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    1 (   1 expanded)
%              Number of leaves         :    1 (   1 expanded)
%              Depth                    :    0
%              Number of atoms          :    1 (   1 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u9,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (8877)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.47  % (8893)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.47  % (8877)Refutation not found, incomplete strategy% (8877)------------------------------
% 0.21/0.47  % (8877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8877)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (8877)Memory used [KB]: 10618
% 0.21/0.47  % (8877)Time elapsed: 0.064 s
% 0.21/0.47  % (8877)------------------------------
% 0.21/0.47  % (8877)------------------------------
% 0.21/0.47  % (8893)Refutation not found, incomplete strategy% (8893)------------------------------
% 0.21/0.47  % (8893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8893)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (8893)Memory used [KB]: 6140
% 0.21/0.47  % (8893)Time elapsed: 0.067 s
% 0.21/0.47  % (8893)------------------------------
% 0.21/0.47  % (8893)------------------------------
% 0.21/0.51  % (8872)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (8872)Refutation not found, incomplete strategy% (8872)------------------------------
% 0.21/0.51  % (8872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8872)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8872)Memory used [KB]: 6140
% 0.21/0.51  % (8872)Time elapsed: 0.108 s
% 0.21/0.51  % (8872)------------------------------
% 0.21/0.51  % (8872)------------------------------
% 0.21/0.51  % (8873)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (8873)# SZS output start Saturation.
% 0.21/0.51  cnf(u9,negated_conjecture,
% 0.21/0.51      k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  % (8873)# SZS output end Saturation.
% 0.21/0.51  % (8873)------------------------------
% 0.21/0.51  % (8873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8873)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (8873)Memory used [KB]: 6140
% 0.21/0.51  % (8873)Time elapsed: 0.105 s
% 0.21/0.51  % (8873)------------------------------
% 0.21/0.51  % (8873)------------------------------
% 0.21/0.52  % (8867)Success in time 0.16 s
%------------------------------------------------------------------------------
