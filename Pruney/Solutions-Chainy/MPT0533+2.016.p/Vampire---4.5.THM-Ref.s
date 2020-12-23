%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  98 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   18
%              Number of atoms          :  123 ( 345 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f17])).

fof(f17,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(f127,plain,(
    ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f126,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f126,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK3),sK3) ),
    inference(subsumption_resolution,[],[f125,f19])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f125,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK3),sK3)
    | ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f122,f17])).

fof(f122,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK3),sK3)
    | ~ v1_relat_1(sK3)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f70,f60])).

fof(f60,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f58,f17])).

fof(f58,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3)) ),
    inference(resolution,[],[f53,f18])).

fof(f18,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2,X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k8_relat_1(sK0,X1),k8_relat_1(sK1,sK3)) ) ),
    inference(subsumption_resolution,[],[f50,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X1] :
      ( ~ r1_tarski(k8_relat_1(sK0,X1),k8_relat_1(sK1,sK3))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(sK2,X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f45,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

% (12625)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(f45,plain,(
    ! [X0] :
      ( ~ r1_tarski(k8_relat_1(sK0,sK2),X0)
      | ~ r1_tarski(X0,k8_relat_1(sK1,sK3)) ) ),
    inference(subsumption_resolution,[],[f43,f20])).

fof(f20,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_tarski(k8_relat_1(sK0,sK2),X0)
      | ~ r1_tarski(X0,k8_relat_1(sK1,sK3))
      | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X1)
      | ~ r1_tarski(k8_relat_1(sK0,sK2),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X0)
      | ~ r1_tarski(k8_relat_1(sK0,sK2),X0) ) ),
    inference(resolution,[],[f31,f25])).

fof(f31,plain,(
    r2_hidden(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f20,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X1,sK3),k8_relat_1(X2,X0))
      | ~ r1_tarski(k8_relat_1(X1,sK3),X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(subsumption_resolution,[],[f69,f17])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k8_relat_1(X1,sK3),X0)
      | r1_tarski(k8_relat_1(X1,sK3),k8_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f34,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f34,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(k8_relat_1(X4,sK3))
      | ~ v1_relat_1(X5)
      | ~ r1_tarski(k8_relat_1(X4,sK3),X5)
      | r1_tarski(k8_relat_1(X4,sK3),k8_relat_1(X3,X5))
      | ~ r1_tarski(X4,X3) ) ),
    inference(superposition,[],[f24,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,sK3) = k8_relat_1(X1,k8_relat_1(X0,sK3))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f17,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

% (12627)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (12618)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (12624)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (12612)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (12611)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (12629)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (12613)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (12613)Refutation not found, incomplete strategy% (12613)------------------------------
% 0.21/0.51  % (12613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12613)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12613)Memory used [KB]: 6140
% 0.21/0.51  % (12613)Time elapsed: 0.097 s
% 0.21/0.51  % (12613)------------------------------
% 0.21/0.51  % (12613)------------------------------
% 0.21/0.51  % (12629)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (12617)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (12630)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (12616)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (12621)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (12631)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (12632)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (12622)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (12615)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (12619)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (12610)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (12628)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (12633)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (12614)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (12609)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (12620)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (12630)Refutation not found, incomplete strategy% (12630)------------------------------
% 0.21/0.53  % (12630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12630)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12630)Memory used [KB]: 10618
% 0.21/0.53  % (12630)Time elapsed: 0.107 s
% 0.21/0.53  % (12630)------------------------------
% 0.21/0.53  % (12630)------------------------------
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f127,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    v1_relat_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f6])).
% 0.21/0.53  fof(f6,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ~v1_relat_1(sK3)),
% 0.21/0.53    inference(resolution,[],[f126,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ~r1_tarski(k8_relat_1(sK0,sK3),sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f125,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ~r1_tarski(k8_relat_1(sK0,sK3),sK3) | ~r1_tarski(sK0,sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f17])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ~r1_tarski(k8_relat_1(sK0,sK3),sK3) | ~v1_relat_1(sK3) | ~r1_tarski(sK0,sK1)),
% 0.21/0.53    inference(resolution,[],[f70,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ~r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3))),
% 0.21/0.53    inference(subsumption_resolution,[],[f58,f17])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ~v1_relat_1(sK3) | ~r1_tarski(k8_relat_1(sK0,sK3),k8_relat_1(sK1,sK3))),
% 0.21/0.53    inference(resolution,[],[f53,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    r1_tarski(sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(sK2,X1) | ~v1_relat_1(X1) | ~r1_tarski(k8_relat_1(sK0,X1),k8_relat_1(sK1,sK3))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f50,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k8_relat_1(sK0,X1),k8_relat_1(sK1,sK3)) | ~v1_relat_1(X1) | ~r1_tarski(sK2,X1) | ~v1_relat_1(sK2)) )),
% 0.21/0.53    inference(resolution,[],[f45,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~r1_tarski(X1,X2) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  % (12625)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k8_relat_1(sK0,sK2),X0) | ~r1_tarski(X0,k8_relat_1(sK1,sK3))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f43,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k8_relat_1(sK0,sK2),X0) | ~r1_tarski(X0,k8_relat_1(sK1,sK3)) | r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))) )),
% 0.21/0.53    inference(resolution,[],[f42,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X1) | ~r1_tarski(k8_relat_1(sK0,sK2),X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f32,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),X0) | ~r1_tarski(k8_relat_1(sK0,sK2),X0)) )),
% 0.21/0.53    inference(resolution,[],[f31,f25])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    r2_hidden(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),k8_relat_1(sK0,sK2))),
% 0.21/0.53    inference(resolution,[],[f20,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X1,sK3),k8_relat_1(X2,X0)) | ~r1_tarski(k8_relat_1(X1,sK3),X0) | ~v1_relat_1(X0) | ~r1_tarski(X1,X2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f69,f17])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(k8_relat_1(X1,sK3),X0) | r1_tarski(k8_relat_1(X1,sK3),k8_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(sK3)) )),
% 0.21/0.53    inference(resolution,[],[f34,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~v1_relat_1(k8_relat_1(X4,sK3)) | ~v1_relat_1(X5) | ~r1_tarski(k8_relat_1(X4,sK3),X5) | r1_tarski(k8_relat_1(X4,sK3),k8_relat_1(X3,X5)) | ~r1_tarski(X4,X3)) )),
% 0.21/0.53    inference(superposition,[],[f24,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k8_relat_1(X0,sK3) = k8_relat_1(X1,k8_relat_1(X0,sK3)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f17,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  % (12627)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (12629)------------------------------
% 0.21/0.54  % (12629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12629)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (12629)Memory used [KB]: 1791
% 0.21/0.54  % (12629)Time elapsed: 0.107 s
% 0.21/0.54  % (12629)------------------------------
% 0.21/0.54  % (12629)------------------------------
% 0.21/0.54  % (12607)Success in time 0.176 s
%------------------------------------------------------------------------------
