%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 365 expanded)
%              Number of leaves         :    7 (  99 expanded)
%              Depth                    :   23
%              Number of atoms          :  131 ( 843 expanded)
%              Number of equality atoms :   58 ( 350 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f416,plain,(
    $false ),
    inference(subsumption_resolution,[],[f415,f15])).

fof(f15,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f415,plain,(
    ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f363])).

fof(f363,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f40,f360])).

fof(f360,plain,(
    k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f345])).

fof(f345,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f331,f281])).

fof(f281,plain,(
    ! [X1] :
      ( sK1 = k5_xboole_0(X1,k3_xboole_0(X1,X1))
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f279,f270])).

fof(f270,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(sK3(X19,X19,sK1),X20)
      | k1_xboole_0 = sK1
      | sK1 = k5_xboole_0(X19,k3_xboole_0(X19,X19)) ) ),
    inference(resolution,[],[f253,f206])).

fof(f206,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X0,X1),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X0,X1),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
      | r2_hidden(sK3(X0,X0,X1),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1 ) ),
    inference(resolution,[],[f35,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f24,f17])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f23,f17])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f253,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,sK1)
      | ~ r2_hidden(X8,X7)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f38,f244])).

fof(f244,plain,(
    ! [X0] :
      ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f242,f29])).

fof(f29,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(definition_unfolding,[],[f12,f16])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f12,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f242,plain,(
    ! [X18] :
      ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
      | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X18)) ) ),
    inference(duplicate_literal_removal,[],[f237])).

fof(f237,plain,(
    ! [X18] :
      ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X18))
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
      | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X18)) ) ),
    inference(resolution,[],[f209,f213])).

fof(f213,plain,(
    ! [X14] :
      ( ~ r2_hidden(sK3(sK1,X14,sK1),k3_subset_1(sK0,sK1))
      | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X14)) ) ),
    inference(resolution,[],[f204,f55])).

fof(f55,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k3_subset_1(sK0,sK1)) ) ),
    inference(superposition,[],[f38,f53])).

fof(f53,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f30,f14])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f18,f17])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f204,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(factoring,[],[f35])).

fof(f209,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK3(X4,X5,X4),X6)
      | k5_xboole_0(X4,k3_xboole_0(X4,X5)) = X4
      | ~ r1_tarski(X4,X6) ) ),
    inference(resolution,[],[f204,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f17])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f279,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK1
      | sK1 = k5_xboole_0(X1,k3_xboole_0(X1,X1))
      | r2_hidden(sK3(X1,X1,sK1),X1) ) ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK1
      | sK1 = k5_xboole_0(X1,k3_xboole_0(X1,X1))
      | r2_hidden(sK3(X1,X1,sK1),X1)
      | sK1 = k5_xboole_0(X1,k3_xboole_0(X1,X1)) ) ),
    inference(resolution,[],[f270,f35])).

fof(f331,plain,(
    ! [X7] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f302,f15])).

fof(f302,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(X9,sK1)
      | k5_xboole_0(X9,k3_xboole_0(X9,X10)) = X9
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f294,f209])).

fof(f294,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f284,f253])).

fof(f284,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(X5,X4)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f39,f281])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f17])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f28])).

fof(f28,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f13,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:18:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.53  % (9185)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (9193)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (9201)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (9193)Refutation not found, incomplete strategy% (9193)------------------------------
% 0.21/0.55  % (9193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9193)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9193)Memory used [KB]: 10746
% 0.21/0.55  % (9193)Time elapsed: 0.128 s
% 0.21/0.55  % (9193)------------------------------
% 0.21/0.55  % (9193)------------------------------
% 0.21/0.56  % (9180)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (9195)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (9195)Refutation not found, incomplete strategy% (9195)------------------------------
% 0.21/0.56  % (9195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9195)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9195)Memory used [KB]: 10618
% 0.21/0.56  % (9195)Time elapsed: 0.072 s
% 0.21/0.56  % (9195)------------------------------
% 0.21/0.56  % (9195)------------------------------
% 0.21/0.56  % (9174)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (9187)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (9178)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (9197)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (9173)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (9173)Refutation not found, incomplete strategy% (9173)------------------------------
% 0.21/0.57  % (9173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9173)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9173)Memory used [KB]: 1663
% 0.21/0.57  % (9173)Time elapsed: 0.165 s
% 0.21/0.57  % (9173)------------------------------
% 0.21/0.57  % (9173)------------------------------
% 0.21/0.57  % (9189)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (9179)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (9190)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.58  % (9188)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (9192)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.58  % (9188)Refutation not found, incomplete strategy% (9188)------------------------------
% 0.21/0.58  % (9188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9188)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (9188)Memory used [KB]: 6140
% 0.21/0.58  % (9188)Time elapsed: 0.001 s
% 0.21/0.58  % (9188)------------------------------
% 0.21/0.58  % (9188)------------------------------
% 0.21/0.58  % (9181)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (9182)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.58  % (9175)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.58  % (9177)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.59  % (9196)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.59  % (9177)Refutation not found, incomplete strategy% (9177)------------------------------
% 0.21/0.59  % (9177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (9177)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (9177)Memory used [KB]: 6140
% 0.21/0.59  % (9177)Time elapsed: 0.162 s
% 0.21/0.59  % (9177)------------------------------
% 0.21/0.59  % (9177)------------------------------
% 0.21/0.59  % (9200)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.59  % (9176)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.60  % (9198)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.60  % (9179)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f416,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(subsumption_resolution,[],[f415,f15])).
% 0.21/0.60  fof(f15,plain,(
% 0.21/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.60  fof(f415,plain,(
% 0.21/0.60    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f363])).
% 0.21/0.60  fof(f363,plain,(
% 0.21/0.60    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.21/0.60    inference(backward_demodulation,[],[f40,f360])).
% 0.21/0.60  fof(f360,plain,(
% 0.21/0.60    k1_xboole_0 = sK1),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f345])).
% 0.21/0.60  fof(f345,plain,(
% 0.21/0.60    k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.60    inference(superposition,[],[f331,f281])).
% 0.21/0.60  fof(f281,plain,(
% 0.21/0.60    ( ! [X1] : (sK1 = k5_xboole_0(X1,k3_xboole_0(X1,X1)) | k1_xboole_0 = sK1) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f279,f270])).
% 0.21/0.60  fof(f270,plain,(
% 0.21/0.60    ( ! [X19,X20] : (~r2_hidden(sK3(X19,X19,sK1),X20) | k1_xboole_0 = sK1 | sK1 = k5_xboole_0(X19,k3_xboole_0(X19,X19))) )),
% 0.21/0.60    inference(resolution,[],[f253,f206])).
% 0.21/0.60  fof(f206,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r2_hidden(sK3(X0,X0,X1),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f190])).
% 0.21/0.60  fof(f190,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r2_hidden(sK3(X0,X0,X1),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1 | r2_hidden(sK3(X0,X0,X1),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1) )),
% 0.21/0.60    inference(resolution,[],[f35,f34])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 0.21/0.60    inference(definition_unfolding,[],[f24,f17])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 0.21/0.60    inference(definition_unfolding,[],[f23,f17])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f2])).
% 0.21/0.60  fof(f253,plain,(
% 0.21/0.60    ( ! [X8,X7] : (~r2_hidden(X8,sK1) | ~r2_hidden(X8,X7) | k1_xboole_0 = sK1) )),
% 0.21/0.60    inference(superposition,[],[f38,f244])).
% 0.21/0.60  fof(f244,plain,(
% 0.21/0.60    ( ! [X0] : (sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) | k1_xboole_0 = sK1) )),
% 0.21/0.60    inference(resolution,[],[f242,f29])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.21/0.60    inference(definition_unfolding,[],[f12,f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.60  fof(f12,plain,(
% 0.21/0.60    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.60    inference(cnf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,plain,(
% 0.21/0.60    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.60    inference(negated_conjecture,[],[f7])).
% 0.21/0.60  fof(f7,conjecture,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.60  fof(f242,plain,(
% 0.21/0.60    ( ! [X18] : (~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X18))) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f237])).
% 0.21/0.60  fof(f237,plain,(
% 0.21/0.60    ( ! [X18] : (sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X18)) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X18))) )),
% 0.21/0.60    inference(resolution,[],[f209,f213])).
% 0.21/0.60  fof(f213,plain,(
% 0.21/0.60    ( ! [X14] : (~r2_hidden(sK3(sK1,X14,sK1),k3_subset_1(sK0,sK1)) | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,X14))) )),
% 0.21/0.60    inference(resolution,[],[f204,f55])).
% 0.21/0.60  fof(f55,plain,(
% 0.21/0.60    ( ! [X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X1,k3_subset_1(sK0,sK1))) )),
% 0.21/0.60    inference(superposition,[],[f38,f53])).
% 0.21/0.60  fof(f53,plain,(
% 0.21/0.60    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(resolution,[],[f30,f14])).
% 0.21/0.60  fof(f14,plain,(
% 0.21/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.60    inference(cnf_transformation,[],[f9])).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f18,f17])).
% 0.21/0.60  fof(f18,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f10])).
% 0.21/0.60  fof(f10,plain,(
% 0.21/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.60  fof(f204,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.60    inference(factoring,[],[f35])).
% 0.21/0.60  fof(f209,plain,(
% 0.21/0.60    ( ! [X6,X4,X5] : (r2_hidden(sK3(X4,X5,X4),X6) | k5_xboole_0(X4,k3_xboole_0(X4,X5)) = X4 | ~r1_tarski(X4,X6)) )),
% 0.21/0.60    inference(resolution,[],[f204,f19])).
% 0.21/0.60  fof(f19,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f11])).
% 0.21/0.60  fof(f11,plain,(
% 0.21/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 0.21/0.60    inference(equality_resolution,[],[f32])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.21/0.60    inference(definition_unfolding,[],[f26,f17])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f2])).
% 0.21/0.60  fof(f279,plain,(
% 0.21/0.60    ( ! [X1] : (k1_xboole_0 = sK1 | sK1 = k5_xboole_0(X1,k3_xboole_0(X1,X1)) | r2_hidden(sK3(X1,X1,sK1),X1)) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f272])).
% 0.21/0.60  fof(f272,plain,(
% 0.21/0.60    ( ! [X1] : (k1_xboole_0 = sK1 | sK1 = k5_xboole_0(X1,k3_xboole_0(X1,X1)) | r2_hidden(sK3(X1,X1,sK1),X1) | sK1 = k5_xboole_0(X1,k3_xboole_0(X1,X1))) )),
% 0.21/0.60    inference(resolution,[],[f270,f35])).
% 0.21/0.60  fof(f331,plain,(
% 0.21/0.60    ( ! [X7] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)) | k1_xboole_0 = sK1) )),
% 0.21/0.60    inference(resolution,[],[f302,f15])).
% 0.21/0.60  fof(f302,plain,(
% 0.21/0.60    ( ! [X10,X9] : (~r1_tarski(X9,sK1) | k5_xboole_0(X9,k3_xboole_0(X9,X10)) = X9 | k1_xboole_0 = sK1) )),
% 0.21/0.60    inference(resolution,[],[f294,f209])).
% 0.21/0.60  fof(f294,plain,(
% 0.21/0.60    ( ! [X5] : (~r2_hidden(X5,sK1) | k1_xboole_0 = sK1) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f284,f253])).
% 0.21/0.60  fof(f284,plain,(
% 0.21/0.60    ( ! [X4,X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,X4) | k1_xboole_0 = sK1) )),
% 0.21/0.60    inference(superposition,[],[f39,f281])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 0.21/0.60    inference(equality_resolution,[],[f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.21/0.60    inference(definition_unfolding,[],[f25,f17])).
% 0.21/0.60  fof(f25,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f2])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.21/0.60    inference(inner_rewriting,[],[f28])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.60    inference(definition_unfolding,[],[f13,f16])).
% 0.21/0.60  fof(f13,plain,(
% 0.21/0.60    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.60    inference(cnf_transformation,[],[f9])).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (9179)------------------------------
% 0.21/0.60  % (9179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (9179)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (9179)Memory used [KB]: 6524
% 0.21/0.60  % (9179)Time elapsed: 0.102 s
% 0.21/0.60  % (9179)------------------------------
% 0.21/0.60  % (9179)------------------------------
% 0.21/0.60  % (9190)Refutation not found, incomplete strategy% (9190)------------------------------
% 0.21/0.60  % (9190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (9190)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (9190)Memory used [KB]: 10618
% 0.21/0.60  % (9190)Time elapsed: 0.178 s
% 0.21/0.60  % (9190)------------------------------
% 0.21/0.60  % (9190)------------------------------
% 0.21/0.60  % (9202)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.60  % (9182)Refutation not found, incomplete strategy% (9182)------------------------------
% 0.21/0.60  % (9182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (9194)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.60  % (9182)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (9182)Memory used [KB]: 10618
% 0.21/0.60  % (9182)Time elapsed: 0.180 s
% 0.21/0.60  % (9182)------------------------------
% 0.21/0.60  % (9182)------------------------------
% 0.21/0.60  % (9184)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.60  % (9184)Refutation not found, incomplete strategy% (9184)------------------------------
% 0.21/0.60  % (9184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (9184)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (9184)Memory used [KB]: 10618
% 0.21/0.60  % (9184)Time elapsed: 0.185 s
% 0.21/0.60  % (9184)------------------------------
% 0.21/0.60  % (9184)------------------------------
% 0.21/0.60  % (9191)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.61  % (9186)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.81/0.62  % (9199)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.81/0.62  % (9172)Success in time 0.248 s
%------------------------------------------------------------------------------
