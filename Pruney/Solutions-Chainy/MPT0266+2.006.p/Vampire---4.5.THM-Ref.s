%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  64 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   83 ( 119 expanded)
%              Number of equality atoms :   33 (  64 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f775,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f71,f82,f84,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f84,plain,(
    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(superposition,[],[f65,f56])).

fof(f56,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f28,f55,f45,f55])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(f65,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X0,X1),sK2)) ),
    inference(unit_resulting_resolution,[],[f73,f29,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f29,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f35,f54])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X4,X2)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X4,X2) != X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:11:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.56  % (21384)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (21385)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (21383)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (21401)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (21400)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (21393)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (21392)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.57  % (21391)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.58  % (21399)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (21381)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.59  % (21382)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.59  % (21394)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.59  % (21402)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.59  % (21379)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.60  % (21389)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.60  % (21387)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.60  % (21378)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.60  % (21386)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.60  % (21395)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.60  % (21394)Refutation not found, incomplete strategy% (21394)------------------------------
% 0.22/0.60  % (21394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (21394)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (21394)Memory used [KB]: 10618
% 0.22/0.60  % (21394)Time elapsed: 0.136 s
% 0.22/0.60  % (21394)------------------------------
% 0.22/0.60  % (21394)------------------------------
% 0.22/0.61  % (21398)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.61  % (21404)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.61  % (21396)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.61  % (21403)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.61  % (21390)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.61  % (21405)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.61  % (21388)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.62  % (21380)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.62  % (21397)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.62  % (21406)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.62  % (21377)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.63  % (21381)Refutation found. Thanks to Tanya!
% 0.22/0.63  % SZS status Theorem for theBenchmark
% 0.22/0.64  % SZS output start Proof for theBenchmark
% 0.22/0.64  fof(f775,plain,(
% 0.22/0.64    $false),
% 0.22/0.64    inference(unit_resulting_resolution,[],[f71,f82,f84,f42])).
% 0.22/0.64  fof(f42,plain,(
% 0.22/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.64    inference(cnf_transformation,[],[f27])).
% 0.22/0.64  fof(f27,plain,(
% 0.22/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.64    inference(ennf_transformation,[],[f21])).
% 0.22/0.64  fof(f21,plain,(
% 0.22/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.64    inference(rectify,[],[f4])).
% 0.22/0.64  fof(f4,axiom,(
% 0.22/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.64  fof(f84,plain,(
% 0.22/0.64    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.22/0.64    inference(superposition,[],[f65,f56])).
% 0.22/0.64  fof(f56,plain,(
% 0.22/0.64    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.22/0.64    inference(definition_unfolding,[],[f28,f55,f45,f55])).
% 0.22/0.64  fof(f45,plain,(
% 0.22/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.22/0.64    inference(cnf_transformation,[],[f9])).
% 0.22/0.64  fof(f9,axiom,(
% 0.22/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.22/0.64  fof(f55,plain,(
% 0.22/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.64    inference(definition_unfolding,[],[f48,f54])).
% 0.22/0.64  fof(f54,plain,(
% 0.22/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.64    inference(definition_unfolding,[],[f50,f53])).
% 0.22/0.64  fof(f53,plain,(
% 0.22/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.64    inference(cnf_transformation,[],[f14])).
% 0.22/0.64  fof(f14,axiom,(
% 0.22/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.64  fof(f50,plain,(
% 0.22/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.64    inference(cnf_transformation,[],[f13])).
% 0.22/0.64  fof(f13,axiom,(
% 0.22/0.64    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.64  fof(f48,plain,(
% 0.22/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.64    inference(cnf_transformation,[],[f12])).
% 0.22/0.64  fof(f12,axiom,(
% 0.22/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.64  fof(f28,plain,(
% 0.22/0.64    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.22/0.64    inference(cnf_transformation,[],[f24])).
% 0.22/0.64  fof(f24,plain,(
% 0.22/0.64    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.64    inference(ennf_transformation,[],[f20])).
% 0.22/0.64  fof(f20,negated_conjecture,(
% 0.22/0.64    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 0.22/0.64    inference(negated_conjecture,[],[f19])).
% 0.22/0.64  fof(f19,conjecture,(
% 0.22/0.64    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 0.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).
% 0.22/0.64  fof(f65,plain,(
% 0.22/0.64    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)),k5_xboole_0(X0,X1))) )),
% 0.22/0.64    inference(definition_unfolding,[],[f46,f45])).
% 0.22/0.64  fof(f46,plain,(
% 0.22/0.64    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.22/0.64    inference(cnf_transformation,[],[f5])).
% 0.22/0.64  fof(f5,axiom,(
% 0.22/0.64    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.22/0.64  fof(f82,plain,(
% 0.22/0.64    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,X0,X1),sK2))) )),
% 0.22/0.64    inference(unit_resulting_resolution,[],[f73,f29,f41])).
% 0.22/0.64  fof(f41,plain,(
% 0.22/0.64    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 0.22/0.64    inference(cnf_transformation,[],[f26])).
% 0.22/0.64  fof(f26,plain,(
% 0.22/0.64    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.22/0.64    inference(ennf_transformation,[],[f3])).
% 0.22/0.64  fof(f3,axiom,(
% 0.22/0.64    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.22/0.64  fof(f29,plain,(
% 0.22/0.64    ~r2_hidden(sK0,sK2)),
% 0.22/0.64    inference(cnf_transformation,[],[f24])).
% 0.22/0.64  fof(f73,plain,(
% 0.22/0.64    ( ! [X4,X2,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2))) )),
% 0.22/0.64    inference(equality_resolution,[],[f72])).
% 0.22/0.64  fof(f72,plain,(
% 0.22/0.64    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X4,X4,X4,X1,X2) != X3) )),
% 0.22/0.64    inference(equality_resolution,[],[f59])).
% 0.22/0.64  fof(f59,plain,(
% 0.22/0.64    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.22/0.64    inference(definition_unfolding,[],[f35,f54])).
% 0.22/0.64  fof(f35,plain,(
% 0.22/0.64    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.64    inference(cnf_transformation,[],[f25])).
% 0.22/0.64  fof(f25,plain,(
% 0.22/0.64    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.64    inference(ennf_transformation,[],[f11])).
% 0.22/0.64  fof(f11,axiom,(
% 0.22/0.64    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.64  fof(f71,plain,(
% 0.22/0.64    ( ! [X4,X2,X0] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X4,X2))) )),
% 0.22/0.64    inference(equality_resolution,[],[f70])).
% 0.22/0.64  fof(f70,plain,(
% 0.22/0.64    ( ! [X4,X2,X0,X3] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X4,X2) != X3) )),
% 0.22/0.64    inference(equality_resolution,[],[f58])).
% 0.22/0.64  fof(f58,plain,(
% 0.22/0.64    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.22/0.64    inference(definition_unfolding,[],[f36,f54])).
% 0.22/0.64  fof(f36,plain,(
% 0.22/0.64    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.64    inference(cnf_transformation,[],[f25])).
% 0.22/0.64  % SZS output end Proof for theBenchmark
% 0.22/0.64  % (21381)------------------------------
% 0.22/0.64  % (21381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.64  % (21381)Termination reason: Refutation
% 0.22/0.64  
% 0.22/0.64  % (21381)Memory used [KB]: 6780
% 0.22/0.64  % (21381)Time elapsed: 0.188 s
% 0.22/0.64  % (21381)------------------------------
% 0.22/0.64  % (21381)------------------------------
% 0.22/0.64  % (21376)Success in time 0.274 s
%------------------------------------------------------------------------------
