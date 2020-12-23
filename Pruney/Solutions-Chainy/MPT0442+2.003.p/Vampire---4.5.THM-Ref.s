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
% DateTime   : Thu Dec  3 12:47:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 106 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 313 expanded)
%              Number of equality atoms :   14 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f340,plain,(
    $false ),
    inference(global_subsumption,[],[f292,f339])).

fof(f339,plain,(
    ~ r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f329,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP4(X2,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f329,plain,(
    ~ sP4(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f324,f151])).

fof(f151,plain,(
    ! [X0] :
      ( ~ sP4(X0,sK0)
      | sP4(X0,sK1) ) ),
    inference(resolution,[],[f146,f34])).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f146,plain,(
    ! [X10] :
      ( r2_hidden(k4_tarski(sK5(sK0,X10),X10),sK1)
      | ~ sP4(X10,sK0) ) ),
    inference(resolution,[],[f33,f137])).

fof(f137,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f133,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f133,plain,(
    ! [X5] :
      ( ~ sP7(X5,sK1,sK0)
      | r2_hidden(X5,sK1) ) ),
    inference(superposition,[],[f53,f55])).

fof(f55,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f324,plain,(
    ~ sP4(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f291,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ sP4(X2,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f291,plain,(
    ~ r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f277,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f277,plain,(
    ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f271,f20])).

fof(f20,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f271,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f25,f257])).

fof(f257,plain,(
    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f240,f55])).

fof(f240,plain,(
    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f23,f21,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f292,plain,(
    r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f277,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (30372)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (30381)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (30364)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (30359)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (30361)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (30373)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (30381)Refutation not found, incomplete strategy% (30381)------------------------------
% 0.22/0.51  % (30381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30358)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (30362)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (30382)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (30378)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (30365)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (30371)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (30381)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30381)Memory used [KB]: 10746
% 0.22/0.52  % (30381)Time elapsed: 0.105 s
% 0.22/0.52  % (30381)------------------------------
% 0.22/0.52  % (30381)------------------------------
% 0.22/0.52  % (30375)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (30370)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (30369)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (30388)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (30369)Refutation not found, incomplete strategy% (30369)------------------------------
% 0.22/0.53  % (30369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30369)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30369)Memory used [KB]: 10618
% 0.22/0.53  % (30369)Time elapsed: 0.127 s
% 0.22/0.53  % (30369)------------------------------
% 0.22/0.53  % (30369)------------------------------
% 0.22/0.53  % (30366)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (30380)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (30376)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (30383)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (30379)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (30377)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (30360)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (30363)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (30385)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (30367)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (30386)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (30368)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (30387)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (30384)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (30383)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 1.52/0.56  % SZS output start Proof for theBenchmark
% 1.52/0.56  fof(f340,plain,(
% 1.52/0.56    $false),
% 1.52/0.56    inference(global_subsumption,[],[f292,f339])).
% 1.52/0.56  fof(f339,plain,(
% 1.52/0.56    ~r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK0))),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f329,f50])).
% 1.52/0.56  fof(f50,plain,(
% 1.52/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP4(X2,X0)) )),
% 1.52/0.56    inference(equality_resolution,[],[f36])).
% 1.52/0.56  fof(f36,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (sP4(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.52/0.56    inference(cnf_transformation,[],[f8])).
% 1.52/0.56  fof(f8,axiom,(
% 1.52/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.52/0.56  fof(f329,plain,(
% 1.52/0.56    ~sP4(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),sK0)),
% 1.52/0.56    inference(unit_resulting_resolution,[],[f324,f151])).
% 1.52/0.56  fof(f151,plain,(
% 1.52/0.56    ( ! [X0] : (~sP4(X0,sK0) | sP4(X0,sK1)) )),
% 1.52/0.56    inference(resolution,[],[f146,f34])).
% 1.52/0.56  fof(f34,plain,(
% 1.52/0.56    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | sP4(X2,X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f8])).
% 1.52/0.56  fof(f146,plain,(
% 1.52/0.56    ( ! [X10] : (r2_hidden(k4_tarski(sK5(sK0,X10),X10),sK1) | ~sP4(X10,sK0)) )),
% 1.52/0.56    inference(resolution,[],[f33,f137])).
% 1.52/0.56  fof(f137,plain,(
% 1.52/0.56    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(X1,sK1)) )),
% 1.52/0.56    inference(resolution,[],[f133,f41])).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.52/0.57  fof(f133,plain,(
% 1.52/0.57    ( ! [X5] : (~sP7(X5,sK1,sK0) | r2_hidden(X5,sK1)) )),
% 1.52/0.57    inference(superposition,[],[f53,f55])).
% 1.52/0.57  fof(f55,plain,(
% 1.52/0.57    sK1 = k2_xboole_0(sK0,sK1)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f22,f26])).
% 1.52/0.57  fof(f26,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f15])).
% 1.52/0.57  fof(f15,plain,(
% 1.52/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    r1_tarski(sK0,sK1)),
% 1.52/0.57    inference(cnf_transformation,[],[f13])).
% 1.52/0.57  fof(f13,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : ((~r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.52/0.57    inference(flattening,[],[f12])).
% 1.52/0.57  fof(f12,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : (((~r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f11])).
% 1.52/0.57  fof(f11,negated_conjecture,(
% 1.52/0.57    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.52/0.57    inference(negated_conjecture,[],[f10])).
% 1.52/0.57  fof(f10,conjecture,(
% 1.52/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.52/0.57  fof(f53,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~sP7(X3,X1,X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.52/0.57    inference(cnf_transformation,[],[f2])).
% 1.52/0.57  fof(f33,plain,(
% 1.52/0.57    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~sP4(X2,X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f8])).
% 1.52/0.57  fof(f324,plain,(
% 1.52/0.57    ~sP4(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),sK1)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f291,f51])).
% 1.52/0.57  fof(f51,plain,(
% 1.52/0.57    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~sP4(X2,X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f35])).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~sP4(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f8])).
% 1.52/0.57  fof(f291,plain,(
% 1.52/0.57    ~r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f277,f32])).
% 1.52/0.57  fof(f32,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f16,plain,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.57  fof(f277,plain,(
% 1.52/0.57    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f271,f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.52/0.57    inference(cnf_transformation,[],[f13])).
% 1.52/0.57  fof(f271,plain,(
% 1.52/0.57    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 1.52/0.57    inference(superposition,[],[f25,f257])).
% 1.52/0.57  fof(f257,plain,(
% 1.52/0.57    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 1.52/0.57    inference(forward_demodulation,[],[f240,f55])).
% 1.52/0.57  fof(f240,plain,(
% 1.52/0.57    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f23,f21,f24])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f14])).
% 1.52/0.57  fof(f14,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,axiom,(
% 1.52/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    v1_relat_1(sK1)),
% 1.52/0.57    inference(cnf_transformation,[],[f13])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    v1_relat_1(sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f13])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f6])).
% 1.52/0.57  fof(f6,axiom,(
% 1.52/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.52/0.57  fof(f292,plain,(
% 1.52/0.57    r2_hidden(sK2(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK0))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f277,f31])).
% 1.52/0.57  fof(f31,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (30383)------------------------------
% 1.52/0.57  % (30383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (30383)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (30383)Memory used [KB]: 6524
% 1.52/0.57  % (30383)Time elapsed: 0.145 s
% 1.52/0.57  % (30383)------------------------------
% 1.52/0.57  % (30383)------------------------------
% 1.52/0.57  % (30475)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.52/0.57  % (30354)Success in time 0.205 s
%------------------------------------------------------------------------------
