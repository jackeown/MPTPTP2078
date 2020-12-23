%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:14 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u22,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ r2_hidden(X2,k1_xboole_0) )).

cnf(u18,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK2(X0),X1)
    | k1_xboole_0 = X0 )).

cnf(u16,axiom,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 )).

cnf(u17,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u21,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u24,negated_conjecture,
    ( k1_xboole_0 != k1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (7154)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.45  % (7154)Refutation not found, incomplete strategy% (7154)------------------------------
% 0.19/0.45  % (7154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (7154)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (7154)Memory used [KB]: 10618
% 0.19/0.45  % (7154)Time elapsed: 0.053 s
% 0.19/0.45  % (7154)------------------------------
% 0.19/0.45  % (7154)------------------------------
% 0.19/0.46  % (7151)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.46  % (7167)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.46  % (7151)Refutation not found, incomplete strategy% (7151)------------------------------
% 0.19/0.46  % (7151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (7151)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (7151)Memory used [KB]: 6012
% 0.19/0.46  % (7151)Time elapsed: 0.047 s
% 0.19/0.46  % (7151)------------------------------
% 0.19/0.46  % (7151)------------------------------
% 0.19/0.46  % (7167)Refutation not found, incomplete strategy% (7167)------------------------------
% 0.19/0.46  % (7167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (7167)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (7167)Memory used [KB]: 10618
% 0.19/0.46  % (7167)Time elapsed: 0.064 s
% 0.19/0.46  % (7167)------------------------------
% 0.19/0.46  % (7167)------------------------------
% 0.19/0.46  % (7165)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.46  % (7165)Refutation not found, incomplete strategy% (7165)------------------------------
% 0.19/0.46  % (7165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (7165)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (7165)Memory used [KB]: 10618
% 0.19/0.46  % (7165)Time elapsed: 0.060 s
% 0.19/0.46  % (7165)------------------------------
% 0.19/0.46  % (7165)------------------------------
% 0.19/0.47  % (7158)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.47  % (7168)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.47  % (7168)# SZS output start Saturation.
% 0.19/0.47  cnf(u23,negated_conjecture,
% 0.19/0.47      m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.19/0.47  
% 0.19/0.47  cnf(u22,negated_conjecture,
% 0.19/0.47      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_xboole_0)).
% 0.19/0.47  
% 0.19/0.47  cnf(u18,axiom,
% 0.19/0.47      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK2(X0),X1) | k1_xboole_0 = X0).
% 0.19/0.47  
% 0.19/0.47  cnf(u16,axiom,
% 0.19/0.47      r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0).
% 0.19/0.47  
% 0.19/0.47  cnf(u17,axiom,
% 0.19/0.47      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.19/0.47  
% 0.19/0.47  cnf(u21,negated_conjecture,
% 0.19/0.47      k1_xboole_0 = sK1).
% 0.19/0.47  
% 0.19/0.47  cnf(u24,negated_conjecture,
% 0.19/0.47      k1_xboole_0 != k1_struct_0(sK0)).
% 0.19/0.47  
% 0.19/0.47  % (7168)# SZS output end Saturation.
% 0.19/0.47  % (7168)------------------------------
% 0.19/0.47  % (7168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (7168)Termination reason: Satisfiable
% 0.19/0.47  
% 0.19/0.47  % (7168)Memory used [KB]: 1663
% 0.19/0.47  % (7168)Time elapsed: 0.060 s
% 0.19/0.47  % (7168)------------------------------
% 0.19/0.47  % (7168)------------------------------
% 0.19/0.47  % (7150)Success in time 0.118 s
%------------------------------------------------------------------------------
