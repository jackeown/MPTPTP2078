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
% DateTime   : Thu Dec  3 13:08:48 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u151,negated_conjecture,
    ( ~ ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u150,negated_conjecture,
    ( ~ ( k1_xboole_0 != k7_subset_1(sK1,sK1,sK1) )
    | k1_xboole_0 != k7_subset_1(sK1,sK1,sK1) )).

tff(u149,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u148,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u147,axiom,(
    ! [X3,X4] : k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) )).

tff(u146,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

tff(u145,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

tff(u144,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u143,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u142,axiom,(
    ! [X1,X0] : k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))) )).

tff(u141,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

tff(u140,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u139,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(sK1,sK1,X2) )).

tff(u138,negated_conjecture,
    ( u1_struct_0(sK0) != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u137,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u136,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u135,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u134,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u133,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u132,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u131,axiom,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | u1_struct_0(X1) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1))) ) )).

tff(u130,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0)) ) )).

tff(u129,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (28453)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (28443)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (28443)Refutation not found, incomplete strategy% (28443)------------------------------
% 0.20/0.51  % (28443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28453)Refutation not found, incomplete strategy% (28453)------------------------------
% 0.20/0.51  % (28453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28459)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (28443)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28443)Memory used [KB]: 10618
% 0.20/0.51  % (28443)Time elapsed: 0.103 s
% 0.20/0.51  % (28443)------------------------------
% 0.20/0.51  % (28443)------------------------------
% 0.20/0.52  % (28436)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (28442)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (28461)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (28436)Refutation not found, incomplete strategy% (28436)------------------------------
% 0.20/0.52  % (28436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28436)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28436)Memory used [KB]: 10618
% 0.20/0.52  % (28436)Time elapsed: 0.113 s
% 0.20/0.52  % (28436)------------------------------
% 0.20/0.52  % (28436)------------------------------
% 0.20/0.52  % (28445)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (28456)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (28456)Refutation not found, incomplete strategy% (28456)------------------------------
% 0.20/0.52  % (28456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28456)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28456)Memory used [KB]: 10618
% 0.20/0.52  % (28456)Time elapsed: 0.077 s
% 0.20/0.52  % (28456)------------------------------
% 0.20/0.52  % (28456)------------------------------
% 0.20/0.52  % (28445)Refutation not found, incomplete strategy% (28445)------------------------------
% 0.20/0.52  % (28445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28445)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28445)Memory used [KB]: 10618
% 0.20/0.52  % (28459)Refutation not found, incomplete strategy% (28459)------------------------------
% 0.20/0.52  % (28459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28459)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28459)Memory used [KB]: 6268
% 0.20/0.52  % (28459)Time elapsed: 0.117 s
% 0.20/0.52  % (28459)------------------------------
% 0.20/0.52  % (28459)------------------------------
% 0.20/0.52  % (28445)Time elapsed: 0.111 s
% 0.20/0.52  % (28445)------------------------------
% 0.20/0.52  % (28445)------------------------------
% 0.20/0.52  % (28453)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28453)Memory used [KB]: 10746
% 0.20/0.52  % (28453)Time elapsed: 0.105 s
% 0.20/0.52  % (28453)------------------------------
% 0.20/0.52  % (28453)------------------------------
% 0.20/0.52  % (28448)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (28438)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (28438)Refutation not found, incomplete strategy% (28438)------------------------------
% 0.20/0.53  % (28438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28438)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28438)Memory used [KB]: 6140
% 0.20/0.53  % (28438)Time elapsed: 0.125 s
% 0.20/0.53  % (28438)------------------------------
% 0.20/0.53  % (28438)------------------------------
% 0.20/0.53  % (28433)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (28439)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (28433)Refutation not found, incomplete strategy% (28433)------------------------------
% 0.20/0.53  % (28433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28433)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28433)Memory used [KB]: 1663
% 0.20/0.53  % (28433)Time elapsed: 0.123 s
% 0.20/0.53  % (28433)------------------------------
% 0.20/0.53  % (28433)------------------------------
% 0.20/0.53  % (28440)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (28439)Refutation not found, incomplete strategy% (28439)------------------------------
% 0.20/0.53  % (28439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28439)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28439)Memory used [KB]: 6268
% 0.20/0.53  % (28439)Time elapsed: 0.124 s
% 0.20/0.53  % (28439)------------------------------
% 0.20/0.53  % (28439)------------------------------
% 0.20/0.53  % (28462)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (28437)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (28434)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (28463)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (28444)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (28454)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (28458)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (28442)Refutation not found, incomplete strategy% (28442)------------------------------
% 0.20/0.54  % (28442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (28442)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28442)Memory used [KB]: 10618
% 0.20/0.54  % (28442)Time elapsed: 0.133 s
% 0.20/0.54  % (28442)------------------------------
% 0.20/0.54  % (28442)------------------------------
% 0.20/0.54  % (28444)Refutation not found, incomplete strategy% (28444)------------------------------
% 0.20/0.54  % (28444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (28444)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28444)Memory used [KB]: 10618
% 0.20/0.54  % (28444)Time elapsed: 0.132 s
% 0.20/0.54  % (28444)------------------------------
% 0.20/0.54  % (28444)------------------------------
% 0.20/0.54  % (28454)Refutation not found, incomplete strategy% (28454)------------------------------
% 0.20/0.54  % (28454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (28454)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28454)Memory used [KB]: 10746
% 0.20/0.54  % (28454)Time elapsed: 0.140 s
% 0.20/0.54  % (28454)------------------------------
% 0.20/0.54  % (28454)------------------------------
% 0.20/0.54  % (28446)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (28441)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (28455)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (28450)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (28460)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (28455)Refutation not found, incomplete strategy% (28455)------------------------------
% 0.20/0.54  % (28455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (28455)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28455)Memory used [KB]: 1663
% 0.20/0.54  % (28455)Time elapsed: 0.137 s
% 0.20/0.54  % (28455)------------------------------
% 0.20/0.54  % (28455)------------------------------
% 0.20/0.54  % (28441)Refutation not found, incomplete strategy% (28441)------------------------------
% 0.20/0.54  % (28441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (28441)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28441)Memory used [KB]: 6268
% 0.20/0.54  % (28441)Time elapsed: 0.137 s
% 0.20/0.54  % (28441)------------------------------
% 0.20/0.54  % (28441)------------------------------
% 0.20/0.54  % (28446)Refutation not found, incomplete strategy% (28446)------------------------------
% 0.20/0.54  % (28446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (28446)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28446)Memory used [KB]: 6268
% 0.20/0.54  % (28446)Time elapsed: 0.142 s
% 0.20/0.54  % (28446)------------------------------
% 0.20/0.54  % (28446)------------------------------
% 0.20/0.55  % (28460)Refutation not found, incomplete strategy% (28460)------------------------------
% 0.20/0.55  % (28460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28460)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (28460)Memory used [KB]: 10746
% 0.20/0.55  % (28460)Time elapsed: 0.148 s
% 0.20/0.55  % (28460)------------------------------
% 0.20/0.55  % (28460)------------------------------
% 0.20/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.55  % (28450)# SZS output start Saturation.
% 0.20/0.55  tff(u151,negated_conjecture,
% 0.20/0.55      ((~(k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u150,negated_conjecture,
% 0.20/0.55      ((~(k1_xboole_0 != k7_subset_1(sK1,sK1,sK1))) | (k1_xboole_0 != k7_subset_1(sK1,sK1,sK1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u149,negated_conjecture,
% 0.20/0.55      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u148,axiom,
% 0.20/0.55      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u147,axiom,
% 0.20/0.55      (![X3, X4] : ((k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))))))).
% 0.20/0.55  
% 0.20/0.55  tff(u146,axiom,
% 0.20/0.55      (![X0] : ((k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u145,axiom,
% 0.20/0.55      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u144,negated_conjecture,
% 0.20/0.55      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u143,axiom,
% 0.20/0.55      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u142,axiom,
% 0.20/0.55      (![X1, X0] : ((k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))))))).
% 0.20/0.55  
% 0.20/0.55  tff(u141,axiom,
% 0.20/0.55      (![X1, X0, X2] : ((k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u140,axiom,
% 0.20/0.55      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u139,negated_conjecture,
% 0.20/0.55      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X2] : ((k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(sK1,sK1,X2)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u138,negated_conjecture,
% 0.20/0.55      ((~(u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))) | (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u137,negated_conjecture,
% 0.20/0.55      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u136,axiom,
% 0.20/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u135,axiom,
% 0.20/0.55      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u134,axiom,
% 0.20/0.55      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u133,negated_conjecture,
% 0.20/0.55      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u132,axiom,
% 0.20/0.55      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u131,axiom,
% 0.20/0.55      (![X1] : ((~l1_struct_0(X1) | (u1_struct_0(X1) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),u1_struct_0(X1)))))))).
% 0.20/0.55  
% 0.20/0.55  tff(u130,axiom,
% 0.20/0.55      (![X0] : ((~l1_struct_0(X0) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0))))))).
% 0.20/0.55  
% 0.20/0.55  tff(u129,negated_conjecture,
% 0.20/0.55      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.55  
% 0.20/0.55  % (28450)# SZS output end Saturation.
% 0.20/0.55  % (28450)------------------------------
% 0.20/0.55  % (28450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28450)Termination reason: Satisfiable
% 0.20/0.55  
% 0.20/0.55  % (28450)Memory used [KB]: 10746
% 0.20/0.55  % (28450)Time elapsed: 0.139 s
% 0.20/0.55  % (28450)------------------------------
% 0.20/0.55  % (28450)------------------------------
% 0.20/0.55  % (28447)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (28457)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (28452)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (28457)Refutation not found, incomplete strategy% (28457)------------------------------
% 0.20/0.55  % (28457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28437)Refutation not found, incomplete strategy% (28437)------------------------------
% 0.20/0.55  % (28437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (28437)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (28437)Memory used [KB]: 10746
% 0.20/0.55  % (28437)Time elapsed: 0.138 s
% 0.20/0.55  % (28437)------------------------------
% 0.20/0.55  % (28437)------------------------------
% 0.20/0.55  % (28451)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (28451)Refutation not found, incomplete strategy% (28451)------------------------------
% 0.20/0.56  % (28451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (28451)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (28451)Memory used [KB]: 10618
% 0.20/0.56  % (28451)Time elapsed: 0.158 s
% 0.20/0.56  % (28451)------------------------------
% 0.20/0.56  % (28451)------------------------------
% 0.20/0.56  % (28432)Success in time 0.194 s
%------------------------------------------------------------------------------
