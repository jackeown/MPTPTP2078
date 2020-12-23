%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 104 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  115 ( 297 expanded)
%              Number of equality atoms :   41 ( 105 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f283,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f281])).

fof(f281,plain,(
    k9_relat_1(sK1,k2_relat_1(sK0)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(superposition,[],[f25,f280])).

fof(f280,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(resolution,[],[f279,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
        & v1_relat_1(X1) )
   => ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f279,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(resolution,[],[f276,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f276,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))
    | k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f271,f103])).

fof(f103,plain,(
    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(superposition,[],[f95,f36])).

fof(f36,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f95,plain,(
    ! [X0] : k5_relat_1(k5_relat_1(sK0,k6_relat_1(X0)),sK1) = k5_relat_1(sK0,k7_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f91,f41])).

fof(f41,plain,(
    ! [X6] : k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1) ),
    inference(resolution,[],[f32,f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f91,plain,(
    ! [X0] : k5_relat_1(k5_relat_1(sK0,k6_relat_1(X0)),sK1) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(X0),sK1)) ),
    inference(resolution,[],[f67,f26])).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f67,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(sK0,X5),sK1) = k5_relat_1(sK0,k5_relat_1(X5,sK1)) ) ),
    inference(resolution,[],[f56,f23])).

fof(f56,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | k5_relat_1(k5_relat_1(X9,X10),sK1) = k5_relat_1(X9,k5_relat_1(X10,sK1)) ) ),
    inference(resolution,[],[f29,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f271,plain,
    ( k9_relat_1(sK1,k2_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0))))
    | ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(resolution,[],[f140,f23])).

fof(f140,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k2_relat_1(k5_relat_1(X6,k7_relat_1(sK1,k2_relat_1(X6)))) = k9_relat_1(sK1,k2_relat_1(X6))
      | ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(X6))) ) ),
    inference(forward_demodulation,[],[f137,f45])).

fof(f45,plain,(
    ! [X6] : k2_relat_1(k7_relat_1(sK1,X6)) = k9_relat_1(sK1,X6) ),
    inference(resolution,[],[f33,f24])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f137,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(X6)))
      | k2_relat_1(k5_relat_1(X6,k7_relat_1(sK1,k2_relat_1(X6)))) = k2_relat_1(k7_relat_1(sK1,k2_relat_1(X6))) ) ),
    inference(resolution,[],[f46,f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X1,k2_relat_1(X0)))
      | k2_relat_1(k5_relat_1(X0,k7_relat_1(X1,k2_relat_1(X0)))) = k2_relat_1(k7_relat_1(X1,k2_relat_1(X0))) ) ),
    inference(resolution,[],[f28,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f25,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (14376)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (14384)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.48  % (14369)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (14365)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.49  % (14373)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.49  % (14374)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.50  % (14385)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (14378)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (14377)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.50  % (14386)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (14380)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (14366)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (14367)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (14367)Refutation not found, incomplete strategy% (14367)------------------------------
% 0.20/0.51  % (14367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14367)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14367)Memory used [KB]: 10490
% 0.20/0.51  % (14367)Time elapsed: 0.094 s
% 0.20/0.51  % (14367)------------------------------
% 0.20/0.51  % (14367)------------------------------
% 0.20/0.51  % (14370)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (14374)Refutation not found, incomplete strategy% (14374)------------------------------
% 0.20/0.51  % (14374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14374)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14374)Memory used [KB]: 10618
% 0.20/0.51  % (14374)Time elapsed: 0.087 s
% 0.20/0.51  % (14374)------------------------------
% 0.20/0.51  % (14374)------------------------------
% 0.20/0.51  % (14379)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.51  % (14382)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.52  % (14371)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (14364)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.52  % (14373)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f283,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f281])).
% 0.20/0.52  fof(f281,plain,(
% 0.20/0.52    k9_relat_1(sK1,k2_relat_1(sK0)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.20/0.52    inference(superposition,[],[f25,f280])).
% 0.20/0.52  fof(f280,plain,(
% 0.20/0.52    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f279,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f21,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) => (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.52    inference(negated_conjecture,[],[f9])).
% 0.20/0.52  fof(f9,conjecture,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.52  fof(f279,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f276,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.52  fof(f276,plain,(
% 0.20/0.52    ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) | k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.20/0.52    inference(forward_demodulation,[],[f271,f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0)))),
% 0.20/0.52    inference(superposition,[],[f95,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.20/0.52    inference(resolution,[],[f27,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    v1_relat_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X0] : (k5_relat_1(k5_relat_1(sK0,k6_relat_1(X0)),sK1) = k5_relat_1(sK0,k7_relat_1(sK1,X0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f91,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X6] : (k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1)) )),
% 0.20/0.52    inference(resolution,[],[f32,f24])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X0] : (k5_relat_1(k5_relat_1(sK0,k6_relat_1(X0)),sK1) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(X0),sK1))) )),
% 0.20/0.52    inference(resolution,[],[f67,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X5] : (~v1_relat_1(X5) | k5_relat_1(k5_relat_1(sK0,X5),sK1) = k5_relat_1(sK0,k5_relat_1(X5,sK1))) )),
% 0.20/0.52    inference(resolution,[],[f56,f23])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X10,X9] : (~v1_relat_1(X9) | ~v1_relat_1(X10) | k5_relat_1(k5_relat_1(X9,X10),sK1) = k5_relat_1(X9,k5_relat_1(X10,sK1))) )),
% 0.20/0.52    inference(resolution,[],[f29,f24])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.20/0.52  fof(f271,plain,(
% 0.20/0.52    k9_relat_1(sK1,k2_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0)))) | ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))),
% 0.20/0.52    inference(resolution,[],[f140,f23])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    ( ! [X6] : (~v1_relat_1(X6) | k2_relat_1(k5_relat_1(X6,k7_relat_1(sK1,k2_relat_1(X6)))) = k9_relat_1(sK1,k2_relat_1(X6)) | ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(X6)))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f137,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X6] : (k2_relat_1(k7_relat_1(sK1,X6)) = k9_relat_1(sK1,X6)) )),
% 0.20/0.52    inference(resolution,[],[f33,f24])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    ( ! [X6] : (~v1_relat_1(X6) | ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(X6))) | k2_relat_1(k5_relat_1(X6,k7_relat_1(sK1,k2_relat_1(X6)))) = k2_relat_1(k7_relat_1(sK1,k2_relat_1(X6)))) )),
% 0.20/0.52    inference(resolution,[],[f46,f24])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X1,k2_relat_1(X0))) | k2_relat_1(k5_relat_1(X0,k7_relat_1(X1,k2_relat_1(X0)))) = k2_relat_1(k7_relat_1(X1,k2_relat_1(X0)))) )),
% 0.20/0.52    inference(resolution,[],[f28,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (14373)------------------------------
% 0.20/0.52  % (14373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14373)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (14373)Memory used [KB]: 2046
% 0.20/0.52  % (14373)Time elapsed: 0.093 s
% 0.20/0.52  % (14373)------------------------------
% 0.20/0.52  % (14373)------------------------------
% 0.20/0.52  % (14363)Success in time 0.16 s
%------------------------------------------------------------------------------
