%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 110 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  113 ( 416 expanded)
%              Number of equality atoms :   53 ( 229 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(subsumption_resolution,[],[f90,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f21,f60])).

fof(f60,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f56,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f2])).

% (2922)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f56,plain,(
    ! [X0] : k1_subset_1(X0) = sK0 ),
    inference(resolution,[],[f53,f22])).

fof(f22,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sK0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sK0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f44,f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f44,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f41,f24])).

% (2909)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f41,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f39,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k2_relat_1(sK1)
    & k1_xboole_0 = k2_relat_1(sK0)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & k1_xboole_0 = k2_relat_1(X1)
            & k1_xboole_0 = k2_relat_1(X0)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(sK0)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( sK0 != X1
        & k1_xboole_0 = k2_relat_1(X1)
        & k1_xboole_0 = k2_relat_1(sK0)
        & v1_relat_1(X1) )
   => ( sK0 != sK1
      & k1_xboole_0 = k2_relat_1(sK1)
      & k1_xboole_0 = k2_relat_1(sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k2_relat_1(X1)
                & k1_xboole_0 = k2_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k1_xboole_0 = k2_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).

fof(f39,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f26,f31])).

fof(f31,plain,(
    sK0 = k8_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f30,f19])).

fof(f19,plain,(
    k1_xboole_0 = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    sK0 = k8_relat_1(k2_relat_1(sK0),sK0) ),
    inference(resolution,[],[f17,f25])).

fof(f25,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k8_relat_1(X1,X0))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc18_relat_1)).

fof(f21,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f87,f23])).

fof(f87,plain,(
    ! [X0] : k1_subset_1(X0) = sK1 ),
    inference(resolution,[],[f55,f22])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sK1 = X0 ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sK1 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f51,f24])).

fof(f51,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f48,f24])).

fof(f48,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f46,f18])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f26,f35])).

fof(f35,plain,(
    sK1 = k8_relat_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f34,f20])).

fof(f20,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    sK1 = k8_relat_1(k2_relat_1(sK1),sK1) ),
    inference(resolution,[],[f18,f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:47:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (2898)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (2908)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (2908)Refutation not found, incomplete strategy% (2908)------------------------------
% 0.21/0.53  % (2908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2908)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2908)Memory used [KB]: 10618
% 0.21/0.53  % (2908)Time elapsed: 0.096 s
% 0.21/0.53  % (2908)------------------------------
% 0.21/0.53  % (2908)------------------------------
% 0.21/0.53  % (2897)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (2897)Refutation not found, incomplete strategy% (2897)------------------------------
% 0.21/0.53  % (2897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2897)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2897)Memory used [KB]: 1663
% 0.21/0.53  % (2897)Time elapsed: 0.099 s
% 0.21/0.53  % (2897)------------------------------
% 0.21/0.53  % (2897)------------------------------
% 0.21/0.53  % (2920)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (2911)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (2920)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (2899)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (2900)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (2913)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (2925)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (2917)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (2914)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (2918)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f90,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(backward_demodulation,[],[f21,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    k1_xboole_0 = sK0),
% 0.21/0.55    inference(forward_demodulation,[],[f56,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  % (2922)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0] : (k1_subset_1(X0) = sK0) )),
% 0.21/0.55    inference(resolution,[],[f53,f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | sK0 = X0) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | sK0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.55    inference(superposition,[],[f44,f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(resolution,[],[f41,f24])).
% 0.21/0.55  % (2909)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    v1_xboole_0(sK0) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f39,f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    v1_relat_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    (sK0 != sK1 & k1_xboole_0 = k2_relat_1(sK1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (sK0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X1] : (sK0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(X1)) => (sK0 != sK1 & k1_xboole_0 = k2_relat_1(sK1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f8])).
% 0.21/0.55  fof(f8,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : ((X0 != X1 & (k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f6])).
% 0.21/0.55  fof(f6,conjecture,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    v1_xboole_0(sK0) | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.21/0.55    inference(superposition,[],[f26,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    sK0 = k8_relat_1(k1_xboole_0,sK0)),
% 0.21/0.55    inference(forward_demodulation,[],[f30,f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    sK0 = k8_relat_1(k2_relat_1(sK0),sK0)),
% 0.21/0.55    inference(resolution,[],[f17,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_xboole_0(k8_relat_1(X1,X0)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1] : ((v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1] : ((v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc18_relat_1)).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    sK0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    k1_xboole_0 = sK1),
% 0.21/0.55    inference(forward_demodulation,[],[f87,f23])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    ( ! [X0] : (k1_subset_1(X0) = sK1) )),
% 0.21/0.55    inference(resolution,[],[f55,f22])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | sK1 = X0) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | sK1 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.55    inference(superposition,[],[f51,f24])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.55    inference(resolution,[],[f48,f24])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f46,f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    v1_relat_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK1)),
% 0.21/0.55    inference(superposition,[],[f26,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    sK1 = k8_relat_1(k1_xboole_0,sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f34,f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    k1_xboole_0 = k2_relat_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    sK1 = k8_relat_1(k2_relat_1(sK1),sK1)),
% 0.21/0.55    inference(resolution,[],[f18,f25])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (2920)------------------------------
% 0.21/0.55  % (2920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2920)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (2920)Memory used [KB]: 1663
% 0.21/0.55  % (2920)Time elapsed: 0.112 s
% 0.21/0.55  % (2920)------------------------------
% 0.21/0.55  % (2920)------------------------------
% 0.21/0.55  % (2896)Success in time 0.188 s
%------------------------------------------------------------------------------
