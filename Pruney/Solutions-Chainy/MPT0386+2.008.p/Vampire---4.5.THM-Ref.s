%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:43 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   40 (  89 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 218 expanded)
%              Number of equality atoms :   25 (  60 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(global_subsumption,[],[f107,f221])).

fof(f221,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f220,f16])).

fof(f16,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f220,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f174,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f18,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f174,plain,(
    ! [X0] : ~ r2_hidden(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f109,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f109,plain,(
    ! [X0] : ~ sP7(sK0,k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f56,f102])).

fof(f102,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f62,f57,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_setfam_1(X0))
      | sP3(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f57,plain,(
    r2_hidden(sK5(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f15,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f15,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f62,plain,(
    ~ sP3(sK5(k1_setfam_1(sK1),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f14,f59,f22])).

fof(f22,plain,(
    ! [X2,X0,X3] :
      ( ~ sP3(X2,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    ~ r2_hidden(sK5(k1_setfam_1(sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f15,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0] : ~ sP7(sK0,sK1,X0) ),
    inference(unit_resulting_resolution,[],[f14,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f107,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f14,f102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (6572)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.53  % (6583)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % (6584)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.53  % (6592)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.28/0.53  % (6592)Refutation not found, incomplete strategy% (6592)------------------------------
% 1.28/0.53  % (6592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (6592)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (6592)Memory used [KB]: 1663
% 1.28/0.53  % (6592)Time elapsed: 0.129 s
% 1.28/0.53  % (6592)------------------------------
% 1.28/0.53  % (6592)------------------------------
% 1.28/0.54  % (6585)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.54  % (6591)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.54  % (6573)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.54  % (6591)Refutation not found, incomplete strategy% (6591)------------------------------
% 1.28/0.54  % (6591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (6591)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (6591)Memory used [KB]: 10618
% 1.28/0.54  % (6591)Time elapsed: 0.131 s
% 1.28/0.54  % (6591)------------------------------
% 1.28/0.54  % (6591)------------------------------
% 1.28/0.54  % (6580)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.54  % (6573)Refutation not found, incomplete strategy% (6573)------------------------------
% 1.28/0.54  % (6573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (6573)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (6573)Memory used [KB]: 10618
% 1.28/0.54  % (6573)Time elapsed: 0.133 s
% 1.28/0.54  % (6573)------------------------------
% 1.28/0.54  % (6573)------------------------------
% 1.45/0.54  % (6600)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.55  % (6599)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.55  % (6581)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.55  % (6593)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.55  % (6593)Refutation not found, incomplete strategy% (6593)------------------------------
% 1.45/0.55  % (6593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (6593)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (6593)Memory used [KB]: 10618
% 1.45/0.55  % (6593)Time elapsed: 0.129 s
% 1.45/0.55  % (6593)------------------------------
% 1.45/0.55  % (6593)------------------------------
% 1.45/0.55  % (6582)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (6575)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.55  % (6589)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.56  % (6574)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.45/0.56  % (6579)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.56  % (6586)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.56  % (6596)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.56  % (6595)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.56  % (6576)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.56  % (6577)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.45/0.56  % (6571)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.45/0.57  % (6597)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.57  % (6587)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.57  % (6588)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.57  % (6598)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.58  % (6594)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.58  % (6590)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.58  % (6595)Refutation found. Thanks to Tanya!
% 1.45/0.58  % SZS status Theorem for theBenchmark
% 1.45/0.58  % SZS output start Proof for theBenchmark
% 1.45/0.58  fof(f222,plain,(
% 1.45/0.58    $false),
% 1.45/0.58    inference(global_subsumption,[],[f107,f221])).
% 1.45/0.58  fof(f221,plain,(
% 1.45/0.58    ~r2_hidden(sK0,k1_xboole_0)),
% 1.45/0.58    inference(forward_demodulation,[],[f220,f16])).
% 1.45/0.58  fof(f16,plain,(
% 1.45/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.45/0.58    inference(cnf_transformation,[],[f6])).
% 1.45/0.58  fof(f6,axiom,(
% 1.45/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.45/0.58  fof(f220,plain,(
% 1.45/0.58    ~r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.45/0.58    inference(superposition,[],[f174,f51])).
% 1.45/0.58  fof(f51,plain,(
% 1.45/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.45/0.58    inference(unit_resulting_resolution,[],[f18,f17])).
% 1.45/0.58  fof(f17,plain,(
% 1.45/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.45/0.58    inference(cnf_transformation,[],[f11])).
% 1.45/0.58  fof(f11,plain,(
% 1.45/0.58    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.45/0.58    inference(ennf_transformation,[],[f5])).
% 1.45/0.58  fof(f5,axiom,(
% 1.45/0.58    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.45/0.58  fof(f18,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f4])).
% 1.45/0.58  fof(f4,axiom,(
% 1.45/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.45/0.58  fof(f174,plain,(
% 1.45/0.58    ( ! [X0] : (~r2_hidden(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) )),
% 1.45/0.58    inference(unit_resulting_resolution,[],[f109,f49])).
% 1.45/0.58  fof(f49,plain,(
% 1.45/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | sP7(X3,X1,X0)) )),
% 1.45/0.58    inference(equality_resolution,[],[f41])).
% 1.45/0.58  fof(f41,plain,(
% 1.45/0.58    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.45/0.58    inference(definition_unfolding,[],[f36,f19])).
% 1.45/0.58  fof(f19,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f3])).
% 1.45/0.58  fof(f3,axiom,(
% 1.45/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.45/0.58  fof(f36,plain,(
% 1.45/0.58    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.45/0.58    inference(cnf_transformation,[],[f2])).
% 1.45/0.58  fof(f2,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.45/0.58  fof(f109,plain,(
% 1.45/0.58    ( ! [X0] : (~sP7(sK0,k1_xboole_0,X0)) )),
% 1.45/0.58    inference(backward_demodulation,[],[f56,f102])).
% 1.45/0.58  fof(f102,plain,(
% 1.45/0.58    k1_xboole_0 = sK1),
% 1.45/0.58    inference(unit_resulting_resolution,[],[f62,f57,f47])).
% 1.45/0.58  fof(f47,plain,(
% 1.45/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k1_setfam_1(X0)) | sP3(X2,X0) | k1_xboole_0 = X0) )),
% 1.45/0.58    inference(equality_resolution,[],[f24])).
% 1.45/0.58  fof(f24,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | sP3(X2,X0) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 1.45/0.58    inference(cnf_transformation,[],[f12])).
% 1.45/0.58  fof(f12,plain,(
% 1.45/0.58    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f7])).
% 1.45/0.58  fof(f7,axiom,(
% 1.45/0.58    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 1.45/0.58  fof(f57,plain,(
% 1.45/0.58    r2_hidden(sK5(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1))),
% 1.45/0.58    inference(unit_resulting_resolution,[],[f15,f30])).
% 1.45/0.58  fof(f30,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f13])).
% 1.45/0.58  fof(f13,plain,(
% 1.45/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.45/0.58    inference(ennf_transformation,[],[f1])).
% 1.45/0.58  fof(f1,axiom,(
% 1.45/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.45/0.58  fof(f15,plain,(
% 1.45/0.58    ~r1_tarski(k1_setfam_1(sK1),sK0)),
% 1.45/0.58    inference(cnf_transformation,[],[f10])).
% 1.45/0.58  fof(f10,plain,(
% 1.45/0.58    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),X0) & r2_hidden(X0,X1))),
% 1.45/0.58    inference(ennf_transformation,[],[f9])).
% 1.45/0.58  fof(f9,negated_conjecture,(
% 1.45/0.58    ~! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.45/0.58    inference(negated_conjecture,[],[f8])).
% 1.45/0.58  fof(f8,conjecture,(
% 1.45/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.45/0.58  fof(f62,plain,(
% 1.45/0.58    ~sP3(sK5(k1_setfam_1(sK1),sK0),sK1)),
% 1.45/0.58    inference(unit_resulting_resolution,[],[f14,f59,f22])).
% 1.45/0.58  fof(f22,plain,(
% 1.45/0.58    ( ! [X2,X0,X3] : (~sP3(X2,X0) | r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f12])).
% 1.45/0.58  fof(f59,plain,(
% 1.45/0.58    ~r2_hidden(sK5(k1_setfam_1(sK1),sK0),sK0)),
% 1.45/0.58    inference(unit_resulting_resolution,[],[f15,f31])).
% 1.45/0.58  fof(f31,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f13])).
% 1.45/0.58  fof(f14,plain,(
% 1.45/0.58    r2_hidden(sK0,sK1)),
% 1.45/0.58    inference(cnf_transformation,[],[f10])).
% 1.45/0.58  fof(f56,plain,(
% 1.45/0.58    ( ! [X0] : (~sP7(sK0,sK1,X0)) )),
% 1.45/0.58    inference(unit_resulting_resolution,[],[f14,f34])).
% 1.45/0.58  fof(f34,plain,(
% 1.45/0.58    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f2])).
% 1.45/0.58  fof(f107,plain,(
% 1.45/0.58    r2_hidden(sK0,k1_xboole_0)),
% 1.45/0.58    inference(backward_demodulation,[],[f14,f102])).
% 1.45/0.58  % SZS output end Proof for theBenchmark
% 1.45/0.58  % (6595)------------------------------
% 1.45/0.58  % (6595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (6595)Termination reason: Refutation
% 1.45/0.58  
% 1.45/0.58  % (6595)Memory used [KB]: 6396
% 1.45/0.58  % (6595)Time elapsed: 0.163 s
% 1.45/0.58  % (6595)------------------------------
% 1.45/0.58  % (6595)------------------------------
% 1.45/0.59  % (6570)Success in time 0.224 s
%------------------------------------------------------------------------------
