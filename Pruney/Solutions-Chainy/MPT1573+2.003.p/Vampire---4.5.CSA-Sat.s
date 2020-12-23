%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:19 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
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
cnf(u7,negated_conjecture,
    ( k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (16025)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.47  % (16017)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.48  % (16025)Refutation not found, incomplete strategy% (16025)------------------------------
% 0.22/0.48  % (16025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16025)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (16025)Memory used [KB]: 10618
% 0.22/0.48  % (16025)Time elapsed: 0.059 s
% 0.22/0.48  % (16025)------------------------------
% 0.22/0.48  % (16025)------------------------------
% 0.22/0.49  % (16009)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.49  % (16009)# SZS output start Saturation.
% 0.22/0.49  cnf(u7,negated_conjecture,
% 0.22/0.49      k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))).
% 0.22/0.49  
% 0.22/0.49  % (16009)# SZS output end Saturation.
% 0.22/0.49  % (16009)------------------------------
% 0.22/0.49  % (16009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16009)Termination reason: Satisfiable
% 0.22/0.49  
% 0.22/0.49  % (16009)Memory used [KB]: 6140
% 0.22/0.49  % (16009)Time elapsed: 0.070 s
% 0.22/0.49  % (16009)------------------------------
% 0.22/0.49  % (16009)------------------------------
% 0.22/0.49  % (16002)Success in time 0.131 s
%------------------------------------------------------------------------------
