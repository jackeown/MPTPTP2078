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
% DateTime   : Thu Dec  3 12:51:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 149 expanded)
%              Number of leaves         :    9 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  114 ( 488 expanded)
%              Number of equality atoms :   44 ( 145 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f278,plain,(
    $false ),
    inference(global_subsumption,[],[f22,f275])).

fof(f275,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f149,f272])).

fof(f272,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f271,f35])).

fof(f35,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0)))) ),
    inference(global_subsumption,[],[f19,f33])).

fof(f33,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0))))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))
    & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
            & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0))
          & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0))
        & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0)))
        & v1_relat_1(X2) )
   => ( k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))
      & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
             => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
           => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f271,plain,(
    k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0)))) = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(superposition,[],[f267,f49])).

fof(f49,plain,(
    ! [X1] : k6_relat_1(k1_relat_1(k7_relat_1(sK2,X1))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(sK2,X1))) ),
    inference(resolution,[],[f39,f20])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(k7_relat_1(X0,X1))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(global_subsumption,[],[f23,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f34,f32])).

fof(f32,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)) ),
    inference(resolution,[],[f28,f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f29,f25])).

fof(f25,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f267,plain,(
    ! [X0] : k5_relat_1(sK1,k6_relat_1(X0)) = k5_relat_1(sK1,k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK2,sK0)))) ),
    inference(superposition,[],[f266,f35])).

fof(f266,plain,(
    ! [X2,X3] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(sK1,k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(forward_demodulation,[],[f265,f32])).

fof(f265,plain,(
    ! [X2,X3] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) ),
    inference(resolution,[],[f219,f23])).

fof(f219,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(sK1,X3),k6_relat_1(X2)) = k5_relat_1(sK1,k5_relat_1(X3,k6_relat_1(X2))) ) ),
    inference(resolution,[],[f67,f23])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(sK1,X1),X0) = k5_relat_1(sK1,k5_relat_1(X1,X0)) ) ),
    inference(resolution,[],[f26,f19])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f149,plain,(
    ! [X0] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0)) ),
    inference(forward_demodulation,[],[f148,f31])).

fof(f31,plain,(
    ! [X1] : k7_relat_1(sK2,X1) = k5_relat_1(k6_relat_1(X1),sK2) ),
    inference(resolution,[],[f28,f20])).

fof(f148,plain,(
    ! [X0] : k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),sK2)) ),
    inference(resolution,[],[f125,f23])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(sK1,X0),sK2) = k5_relat_1(sK1,k5_relat_1(X0,sK2)) ) ),
    inference(resolution,[],[f62,f19])).

fof(f62,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X3,X2),sK2) = k5_relat_1(X3,k5_relat_1(X2,sK2)) ) ),
    inference(resolution,[],[f26,f20])).

fof(f22,plain,(
    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (4463)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.42  % (4457)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.42  % (4456)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (4459)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (4464)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.44  % (4459)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f278,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(global_subsumption,[],[f22,f275])).
% 0.22/0.44  fof(f275,plain,(
% 0.22/0.44    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0))),
% 0.22/0.44    inference(superposition,[],[f149,f272])).
% 0.22/0.44  fof(f272,plain,(
% 0.22/0.44    sK1 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.22/0.44    inference(forward_demodulation,[],[f271,f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0))))),
% 0.22/0.44    inference(global_subsumption,[],[f19,f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    sK1 = k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0)))) | ~v1_relat_1(sK1)),
% 0.22/0.44    inference(resolution,[],[f29,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    (k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ? [X2] : (k5_relat_1(sK1,X2) != k5_relat_1(sK1,k7_relat_1(X2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(X2,sK0))) & v1_relat_1(X2)) => (k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) & r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) & v1_relat_1(sK2))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : ((k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    v1_relat_1(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f271,plain,(
% 0.22/0.44    k5_relat_1(sK1,k6_relat_1(k1_relat_1(k7_relat_1(sK2,sK0)))) = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.22/0.44    inference(superposition,[],[f267,f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X1] : (k6_relat_1(k1_relat_1(k7_relat_1(sK2,X1))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(sK2,X1)))) )),
% 0.22/0.44    inference(resolution,[],[f39,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    v1_relat_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | k6_relat_1(k1_relat_1(k7_relat_1(X0,X1))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(X0,X1)))) )),
% 0.22/0.44    inference(resolution,[],[f37,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 0.22/0.44    inference(global_subsumption,[],[f23,f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f34,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))) )),
% 0.22/0.44    inference(resolution,[],[f28,f23])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(superposition,[],[f29,f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.44  fof(f267,plain,(
% 0.22/0.44    ( ! [X0] : (k5_relat_1(sK1,k6_relat_1(X0)) = k5_relat_1(sK1,k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK2,sK0))))) )),
% 0.22/0.44    inference(superposition,[],[f266,f35])).
% 0.22/0.44  fof(f266,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(sK1,k7_relat_1(k6_relat_1(X3),X2))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f265,f32])).
% 0.22/0.44  fof(f265,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) )),
% 0.22/0.44    inference(resolution,[],[f219,f23])).
% 0.22/0.44  fof(f219,plain,(
% 0.22/0.44    ( ! [X2,X3] : (~v1_relat_1(X3) | k5_relat_1(k5_relat_1(sK1,X3),k6_relat_1(X2)) = k5_relat_1(sK1,k5_relat_1(X3,k6_relat_1(X2)))) )),
% 0.22/0.44    inference(resolution,[],[f67,f23])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK1,X1),X0) = k5_relat_1(sK1,k5_relat_1(X1,X0))) )),
% 0.22/0.44    inference(resolution,[],[f26,f19])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.22/0.44  fof(f149,plain,(
% 0.22/0.44    ( ! [X0] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X0))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f148,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X1] : (k7_relat_1(sK2,X1) = k5_relat_1(k6_relat_1(X1),sK2)) )),
% 0.22/0.44    inference(resolution,[],[f28,f20])).
% 0.22/0.44  fof(f148,plain,(
% 0.22/0.44    ( ! [X0] : (k5_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),sK2) = k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),sK2))) )),
% 0.22/0.44    inference(resolution,[],[f125,f23])).
% 0.22/0.44  fof(f125,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(sK1,X0),sK2) = k5_relat_1(sK1,k5_relat_1(X0,sK2))) )),
% 0.22/0.44    inference(resolution,[],[f62,f19])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X3,X2),sK2) = k5_relat_1(X3,k5_relat_1(X2,sK2))) )),
% 0.22/0.44    inference(resolution,[],[f26,f20])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (4459)------------------------------
% 0.22/0.44  % (4459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (4459)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (4459)Memory used [KB]: 6396
% 0.22/0.44  % (4459)Time elapsed: 0.014 s
% 0.22/0.44  % (4459)------------------------------
% 0.22/0.44  % (4459)------------------------------
% 0.22/0.44  % (4454)Success in time 0.084 s
%------------------------------------------------------------------------------
