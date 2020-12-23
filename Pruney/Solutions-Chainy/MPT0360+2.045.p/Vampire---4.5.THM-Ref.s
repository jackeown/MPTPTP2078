%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:54 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 207 expanded)
%              Number of leaves         :   13 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 442 expanded)
%              Number of equality atoms :   31 ( 143 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1797,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f228,f1761,f1781,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f37,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1781,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f188,f1761,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f188,plain,(
    v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f29,f180])).

fof(f180,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f119,f157])).

fof(f157,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f119,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2)))
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f110,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f110,plain,(
    ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) ),
    inference(unit_resulting_resolution,[],[f28,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f34])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f1761,plain,(
    ! [X0] : ~ m1_subset_1(sK1,k1_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f53,f30,f523])).

fof(f523,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | k1_xboole_0 = X6
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(forward_demodulation,[],[f512,f177])).

fof(f177,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f156,f176])).

fof(f176,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f158,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f158,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f31,f54])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f156,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f512,plain,(
    ! [X6,X5] :
      ( k3_subset_1(X5,X5) = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f510])).

fof(f510,plain,(
    ! [X6,X5] :
      ( k3_subset_1(X5,X5) = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(superposition,[],[f41,f160])).

fof(f160,plain,(
    ! [X4,X3] :
      ( k3_subset_1(X3,X4) = X3
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f34])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f33,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f228,plain,(
    r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f28,f221,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f221,plain,(
    r1_xboole_0(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f181,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k3_subset_1(sK0,sK2))
      | r1_xboole_0(sK1,X0) ) ),
    inference(superposition,[],[f111,f55])).

fof(f111,plain,(
    ! [X0] : r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f29,f57])).

fof(f181,plain,(
    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f110,f157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:31:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (4335)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (4350)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (4343)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (4335)Refutation not found, incomplete strategy% (4335)------------------------------
% 0.21/0.52  % (4335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4341)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (4355)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (4350)Refutation not found, incomplete strategy% (4350)------------------------------
% 0.21/0.53  % (4350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4350)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4350)Memory used [KB]: 10618
% 0.21/0.53  % (4350)Time elapsed: 0.117 s
% 0.21/0.53  % (4350)------------------------------
% 0.21/0.53  % (4350)------------------------------
% 0.21/0.53  % (4339)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (4335)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4335)Memory used [KB]: 10746
% 0.21/0.53  % (4335)Time elapsed: 0.102 s
% 0.21/0.53  % (4335)------------------------------
% 0.21/0.53  % (4335)------------------------------
% 0.21/0.54  % (4334)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (4340)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (4348)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (4338)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (4337)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (4341)Refutation not found, incomplete strategy% (4341)------------------------------
% 0.21/0.54  % (4341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4362)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (4347)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (4357)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (4336)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (4355)Refutation not found, incomplete strategy% (4355)------------------------------
% 0.21/0.55  % (4355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4349)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (4355)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4355)Memory used [KB]: 10746
% 0.21/0.55  % (4355)Time elapsed: 0.119 s
% 0.21/0.55  % (4355)------------------------------
% 0.21/0.55  % (4355)------------------------------
% 0.21/0.55  % (4354)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (4342)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (4356)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (4346)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (4344)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (4358)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.56  % (4341)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (4341)Memory used [KB]: 10746
% 1.49/0.56  % (4341)Time elapsed: 0.119 s
% 1.49/0.56  % (4341)------------------------------
% 1.49/0.56  % (4341)------------------------------
% 1.49/0.56  % (4333)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.49/0.57  % (4351)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.57  % (4352)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.57  % (4359)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.49/0.58  % (4353)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.49/0.58  % (4345)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.68/0.58  % (4360)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.68/0.59  % (4361)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.13/0.67  % (4363)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.13/0.67  % (4357)Refutation found. Thanks to Tanya!
% 2.13/0.67  % SZS status Theorem for theBenchmark
% 2.13/0.67  % SZS output start Proof for theBenchmark
% 2.13/0.67  fof(f1797,plain,(
% 2.13/0.67    $false),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f228,f1761,f1781,f75])).
% 2.13/0.67  fof(f75,plain,(
% 2.13/0.67    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 2.13/0.67    inference(resolution,[],[f37,f62])).
% 2.13/0.67  fof(f62,plain,(
% 2.13/0.67    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 2.13/0.67    inference(equality_resolution,[],[f44])).
% 2.13/0.67  fof(f44,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.13/0.67    inference(cnf_transformation,[],[f9])).
% 2.13/0.67  fof(f9,axiom,(
% 2.13/0.67    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.13/0.67  fof(f37,plain,(
% 2.13/0.67    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f18])).
% 2.13/0.67  fof(f18,plain,(
% 2.13/0.67    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.13/0.67    inference(ennf_transformation,[],[f10])).
% 2.13/0.67  fof(f10,axiom,(
% 2.13/0.67    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.13/0.67  fof(f1781,plain,(
% 2.13/0.67    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,sK1))))) )),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f188,f1761,f35])).
% 2.13/0.67  fof(f35,plain,(
% 2.13/0.67    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f18])).
% 2.13/0.67  fof(f188,plain,(
% 2.13/0.67    v1_xboole_0(sK1)),
% 2.13/0.67    inference(global_subsumption,[],[f29,f180])).
% 2.13/0.67  fof(f180,plain,(
% 2.13/0.67    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | v1_xboole_0(sK1)),
% 2.13/0.67    inference(superposition,[],[f119,f157])).
% 2.13/0.67  fof(f157,plain,(
% 2.13/0.67    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f27,f54])).
% 2.13/0.67  fof(f54,plain,(
% 2.13/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.67    inference(definition_unfolding,[],[f40,f34])).
% 2.13/0.67  fof(f34,plain,(
% 2.13/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f1])).
% 2.13/0.67  fof(f1,axiom,(
% 2.13/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.13/0.67  fof(f40,plain,(
% 2.13/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f21])).
% 2.13/0.67  fof(f21,plain,(
% 2.13/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.67    inference(ennf_transformation,[],[f11])).
% 2.13/0.67  fof(f11,axiom,(
% 2.13/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.13/0.67  fof(f27,plain,(
% 2.13/0.67    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.13/0.67    inference(cnf_transformation,[],[f17])).
% 2.13/0.67  fof(f17,plain,(
% 2.13/0.67    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.13/0.67    inference(flattening,[],[f16])).
% 2.13/0.67  fof(f16,plain,(
% 2.13/0.67    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.13/0.67    inference(ennf_transformation,[],[f15])).
% 2.13/0.67  fof(f15,negated_conjecture,(
% 2.13/0.67    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.13/0.67    inference(negated_conjecture,[],[f14])).
% 2.13/0.67  fof(f14,conjecture,(
% 2.13/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 2.13/0.67  fof(f119,plain,(
% 2.13/0.67    ( ! [X0] : (~r1_tarski(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) | v1_xboole_0(sK1)) )),
% 2.13/0.67    inference(resolution,[],[f110,f39])).
% 2.13/0.67  fof(f39,plain,(
% 2.13/0.67    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f20])).
% 2.13/0.67  fof(f20,plain,(
% 2.13/0.67    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.13/0.67    inference(flattening,[],[f19])).
% 2.13/0.67  fof(f19,plain,(
% 2.13/0.67    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.13/0.67    inference(ennf_transformation,[],[f4])).
% 2.13/0.67  fof(f4,axiom,(
% 2.13/0.67    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 2.13/0.67  fof(f110,plain,(
% 2.13/0.67    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2)))) )),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f28,f57])).
% 2.13/0.67  fof(f57,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.13/0.67    inference(definition_unfolding,[],[f48,f34])).
% 2.13/0.67  fof(f48,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f23])).
% 2.13/0.67  fof(f23,plain,(
% 2.13/0.67    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.13/0.67    inference(ennf_transformation,[],[f7])).
% 2.13/0.67  fof(f7,axiom,(
% 2.13/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.13/0.67  fof(f28,plain,(
% 2.13/0.67    r1_tarski(sK1,sK2)),
% 2.13/0.67    inference(cnf_transformation,[],[f17])).
% 2.13/0.67  fof(f29,plain,(
% 2.13/0.67    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 2.13/0.67    inference(cnf_transformation,[],[f17])).
% 2.13/0.67  fof(f1761,plain,(
% 2.13/0.67    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,sK1))))) )),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f53,f30,f523])).
% 2.13/0.67  fof(f523,plain,(
% 2.13/0.67    ( ! [X6,X5] : (~m1_subset_1(X6,k1_zfmisc_1(X5)) | k1_xboole_0 = X6 | ~r1_xboole_0(X5,X6)) )),
% 2.13/0.67    inference(forward_demodulation,[],[f512,f177])).
% 2.13/0.67  fof(f177,plain,(
% 2.13/0.67    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 2.13/0.67    inference(backward_demodulation,[],[f156,f176])).
% 2.13/0.67  fof(f176,plain,(
% 2.13/0.67    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.13/0.67    inference(forward_demodulation,[],[f158,f52])).
% 2.13/0.67  fof(f52,plain,(
% 2.13/0.67    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.13/0.67    inference(definition_unfolding,[],[f32,f34])).
% 2.13/0.67  fof(f32,plain,(
% 2.13/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.13/0.67    inference(cnf_transformation,[],[f3])).
% 2.13/0.67  fof(f3,axiom,(
% 2.13/0.67    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.13/0.67  fof(f158,plain,(
% 2.13/0.67    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f31,f54])).
% 2.13/0.67  fof(f31,plain,(
% 2.13/0.67    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f13])).
% 2.13/0.67  fof(f13,axiom,(
% 2.13/0.67    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.13/0.67  fof(f156,plain,(
% 2.13/0.67    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f31,f41])).
% 2.13/0.67  fof(f41,plain,(
% 2.13/0.67    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f22])).
% 2.13/0.67  fof(f22,plain,(
% 2.13/0.67    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.67    inference(ennf_transformation,[],[f12])).
% 2.13/0.67  fof(f12,axiom,(
% 2.13/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.13/0.67  fof(f512,plain,(
% 2.13/0.67    ( ! [X6,X5] : (k3_subset_1(X5,X5) = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X5)) | ~r1_xboole_0(X5,X6)) )),
% 2.13/0.67    inference(duplicate_literal_removal,[],[f510])).
% 2.13/0.67  fof(f510,plain,(
% 2.13/0.67    ( ! [X6,X5] : (k3_subset_1(X5,X5) = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(X5)) | ~r1_xboole_0(X5,X6)) )),
% 2.13/0.67    inference(superposition,[],[f41,f160])).
% 2.13/0.67  fof(f160,plain,(
% 2.13/0.67    ( ! [X4,X3] : (k3_subset_1(X3,X4) = X3 | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~r1_xboole_0(X3,X4)) )),
% 2.13/0.67    inference(superposition,[],[f54,f55])).
% 2.13/0.67  fof(f55,plain,(
% 2.13/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.13/0.67    inference(definition_unfolding,[],[f43,f34])).
% 2.13/0.67  fof(f43,plain,(
% 2.13/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f6])).
% 2.13/0.67  fof(f6,axiom,(
% 2.13/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.13/0.67  fof(f30,plain,(
% 2.13/0.67    k1_xboole_0 != sK1),
% 2.13/0.67    inference(cnf_transformation,[],[f17])).
% 2.13/0.67  fof(f53,plain,(
% 2.13/0.67    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.13/0.67    inference(definition_unfolding,[],[f33,f34])).
% 2.13/0.67  fof(f33,plain,(
% 2.13/0.67    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f5])).
% 2.13/0.67  fof(f5,axiom,(
% 2.13/0.67    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.13/0.67  fof(f228,plain,(
% 2.13/0.67    r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)))),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f28,f221,f60])).
% 2.13/0.67  fof(f60,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.13/0.67    inference(definition_unfolding,[],[f51,f34])).
% 2.13/0.67  fof(f51,plain,(
% 2.13/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.13/0.67    inference(cnf_transformation,[],[f26])).
% 2.13/0.67  fof(f26,plain,(
% 2.13/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 2.13/0.67    inference(flattening,[],[f25])).
% 2.13/0.67  fof(f25,plain,(
% 2.13/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.13/0.67    inference(ennf_transformation,[],[f8])).
% 2.13/0.67  fof(f8,axiom,(
% 2.13/0.67    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 2.13/0.67  fof(f221,plain,(
% 2.13/0.67    r1_xboole_0(sK1,sK1)),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f181,f128])).
% 2.13/0.67  fof(f128,plain,(
% 2.13/0.67    ( ! [X0] : (~r1_xboole_0(X0,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,X0)) )),
% 2.13/0.67    inference(superposition,[],[f111,f55])).
% 2.13/0.67  fof(f111,plain,(
% 2.13/0.67    ( ! [X0] : (r1_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(sK0,sK2))))) )),
% 2.13/0.67    inference(unit_resulting_resolution,[],[f29,f57])).
% 2.13/0.67  fof(f181,plain,(
% 2.13/0.67    r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 2.13/0.67    inference(superposition,[],[f110,f157])).
% 2.13/0.67  % SZS output end Proof for theBenchmark
% 2.13/0.67  % (4357)------------------------------
% 2.13/0.67  % (4357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.67  % (4357)Termination reason: Refutation
% 2.13/0.67  
% 2.13/0.67  % (4357)Memory used [KB]: 7419
% 2.13/0.67  % (4357)Time elapsed: 0.246 s
% 2.13/0.67  % (4357)------------------------------
% 2.13/0.67  % (4357)------------------------------
% 2.13/0.67  % (4332)Success in time 0.304 s
%------------------------------------------------------------------------------
