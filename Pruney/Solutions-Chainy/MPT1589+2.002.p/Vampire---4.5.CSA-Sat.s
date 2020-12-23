%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:25 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :    1 (   1 expanded)
%              Number of leaves         :    1 (   1 expanded)
%              Depth                    :    0
%              Number of atoms          :    1 (   1 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u16,negated_conjecture,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:06:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (16192)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (16209)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (16191)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (16191)Refutation not found, incomplete strategy% (16191)------------------------------
% 0.20/0.53  % (16191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16191)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16191)Memory used [KB]: 10618
% 0.20/0.53  % (16191)Time elapsed: 0.111 s
% 0.20/0.53  % (16191)------------------------------
% 0.20/0.53  % (16191)------------------------------
% 0.20/0.53  % (16209)Refutation not found, incomplete strategy% (16209)------------------------------
% 0.20/0.53  % (16209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16209)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16209)Memory used [KB]: 10618
% 0.20/0.53  % (16209)Time elapsed: 0.112 s
% 0.20/0.53  % (16209)------------------------------
% 0.20/0.53  % (16209)------------------------------
% 0.20/0.53  % (16217)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (16217)Refutation not found, incomplete strategy% (16217)------------------------------
% 0.20/0.53  % (16217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16217)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16217)Memory used [KB]: 6140
% 0.20/0.53  % (16217)Time elapsed: 0.110 s
% 0.20/0.53  % (16217)------------------------------
% 0.20/0.53  % (16217)------------------------------
% 0.20/0.53  % (16213)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (16194)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.54  % (16194)# SZS output start Saturation.
% 0.20/0.54  cnf(u16,negated_conjecture,
% 0.20/0.54      k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)).
% 0.20/0.54  
% 0.20/0.54  % (16194)# SZS output end Saturation.
% 0.20/0.54  % (16194)------------------------------
% 0.20/0.54  % (16194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16194)Termination reason: Satisfiable
% 0.20/0.54  
% 0.20/0.54  % (16194)Memory used [KB]: 6140
% 0.20/0.54  % (16194)Time elapsed: 0.126 s
% 0.20/0.54  % (16194)------------------------------
% 0.20/0.54  % (16194)------------------------------
% 0.20/0.54  % (16185)Success in time 0.169 s
%------------------------------------------------------------------------------
