%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:03 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u25,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u28,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,k3_subset_1(X0,X2))
    | r1_xboole_0(X1,X2) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | r1_tarski(X1,k3_subset_1(X0,X2))
    | ~ r1_xboole_0(X1,X2) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u24,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u27,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 )).

cnf(u32,axiom,
    ( ~ r1_xboole_0(X3,X1)
    | ~ r1_xboole_0(X2,X0)
    | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)
    | X1 = X2 )).

cnf(u45,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k2_xboole_0(X0,X2) != X1
    | k1_xboole_0 = X0 )).

cnf(u23,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u38,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u36,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u34,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u26,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u46,axiom,
    ( k1_xboole_0 != k2_xboole_0(X0,X1)
    | k1_xboole_0 = X0 )).

cnf(u22,negated_conjecture,
    ( k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:24:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.48  % (9594)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.49  % (9585)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.49  % (9594)Refutation not found, incomplete strategy% (9594)------------------------------
% 0.19/0.49  % (9594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (9594)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (9594)Memory used [KB]: 10618
% 0.19/0.49  % (9594)Time elapsed: 0.100 s
% 0.19/0.49  % (9594)------------------------------
% 0.19/0.49  % (9594)------------------------------
% 0.19/0.49  % (9606)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.49  % (9585)Refutation not found, incomplete strategy% (9585)------------------------------
% 0.19/0.49  % (9585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (9585)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (9585)Memory used [KB]: 10618
% 0.19/0.49  % (9585)Time elapsed: 0.099 s
% 0.19/0.49  % (9585)------------------------------
% 0.19/0.49  % (9585)------------------------------
% 0.19/0.49  % (9598)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.49  % (9606)Refutation not found, incomplete strategy% (9606)------------------------------
% 0.19/0.49  % (9606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (9606)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (9606)Memory used [KB]: 1663
% 0.19/0.49  % (9606)Time elapsed: 0.052 s
% 0.19/0.49  % (9606)------------------------------
% 0.19/0.49  % (9606)------------------------------
% 0.19/0.49  % (9598)Refutation not found, incomplete strategy% (9598)------------------------------
% 0.19/0.49  % (9598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (9598)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (9598)Memory used [KB]: 6140
% 0.19/0.49  % (9598)Time elapsed: 0.053 s
% 0.19/0.49  % (9598)------------------------------
% 0.19/0.49  % (9598)------------------------------
% 0.19/0.50  % (9590)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.50  % (9590)Refutation not found, incomplete strategy% (9590)------------------------------
% 0.19/0.50  % (9590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (9590)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (9590)Memory used [KB]: 6140
% 0.19/0.50  % (9590)Time elapsed: 0.064 s
% 0.19/0.50  % (9590)------------------------------
% 0.19/0.50  % (9590)------------------------------
% 0.19/0.50  % (9604)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.50  % (9588)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.50  % (9604)Refutation not found, incomplete strategy% (9604)------------------------------
% 0.19/0.50  % (9604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (9604)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (9604)Memory used [KB]: 1663
% 0.19/0.50  % (9604)Time elapsed: 0.110 s
% 0.19/0.50  % (9604)------------------------------
% 0.19/0.50  % (9604)------------------------------
% 0.19/0.50  % (9588)Refutation not found, incomplete strategy% (9588)------------------------------
% 0.19/0.50  % (9588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (9588)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (9588)Memory used [KB]: 6268
% 0.19/0.50  % (9588)Time elapsed: 0.109 s
% 0.19/0.50  % (9588)------------------------------
% 0.19/0.50  % (9588)------------------------------
% 0.19/0.50  % (9589)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.50  % (9605)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.50  % (9586)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.50  % (9589)# SZS output start Saturation.
% 0.19/0.50  cnf(u25,axiom,
% 0.19/0.50      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.19/0.50  
% 0.19/0.50  cnf(u28,axiom,
% 0.19/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u29,axiom,
% 0.19/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.19/0.50  
% 0.19/0.50  cnf(u30,axiom,
% 0.19/0.50      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)).
% 0.19/0.50  
% 0.19/0.50  cnf(u31,axiom,
% 0.19/0.50      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)).
% 0.19/0.50  
% 0.19/0.50  cnf(u42,axiom,
% 0.19/0.50      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u24,axiom,
% 0.19/0.50      r1_xboole_0(X0,k1_xboole_0)).
% 0.19/0.50  
% 0.19/0.50  cnf(u27,axiom,
% 0.19/0.50      ~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0).
% 0.19/0.50  
% 0.19/0.50  cnf(u32,axiom,
% 0.19/0.50      ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) | X1 = X2).
% 0.19/0.50  
% 0.19/0.50  cnf(u45,axiom,
% 0.19/0.50      ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X2) != X1 | k1_xboole_0 = X0).
% 0.19/0.50  
% 0.19/0.50  cnf(u23,axiom,
% 0.19/0.50      r1_tarski(k1_xboole_0,X0)).
% 0.19/0.50  
% 0.19/0.50  cnf(u38,axiom,
% 0.19/0.50      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.19/0.50  
% 0.19/0.50  cnf(u36,axiom,
% 0.19/0.50      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.19/0.50  
% 0.19/0.50  cnf(u34,axiom,
% 0.19/0.50      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.19/0.50  
% 0.19/0.50  cnf(u26,axiom,
% 0.19/0.50      k2_xboole_0(X0,k1_xboole_0) = X0).
% 0.19/0.50  
% 0.19/0.50  cnf(u46,axiom,
% 0.19/0.50      k1_xboole_0 != k2_xboole_0(X0,X1) | k1_xboole_0 = X0).
% 0.19/0.50  
% 0.19/0.50  cnf(u22,negated_conjecture,
% 0.19/0.50      k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0))).
% 0.19/0.50  
% 0.19/0.50  % (9589)# SZS output end Saturation.
% 0.19/0.50  % (9589)------------------------------
% 0.19/0.50  % (9589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (9589)Termination reason: Satisfiable
% 0.19/0.50  
% 0.19/0.50  % (9589)Memory used [KB]: 6140
% 0.19/0.50  % (9589)Time elapsed: 0.107 s
% 0.19/0.50  % (9589)------------------------------
% 0.19/0.50  % (9589)------------------------------
% 0.19/0.50  % (9586)Refutation not found, incomplete strategy% (9586)------------------------------
% 0.19/0.50  % (9586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (9586)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (9586)Memory used [KB]: 6140
% 0.19/0.50  % (9586)Time elapsed: 0.106 s
% 0.19/0.50  % (9586)------------------------------
% 0.19/0.50  % (9586)------------------------------
% 0.19/0.50  % (9605)Refutation not found, incomplete strategy% (9605)------------------------------
% 0.19/0.50  % (9605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (9605)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (9605)Memory used [KB]: 10618
% 0.19/0.50  % (9605)Time elapsed: 0.113 s
% 0.19/0.50  % (9605)------------------------------
% 0.19/0.50  % (9605)------------------------------
% 0.19/0.50  % (9579)Success in time 0.156 s
%------------------------------------------------------------------------------
