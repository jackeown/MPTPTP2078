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
% DateTime   : Thu Dec  3 12:48:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  67 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 192 expanded)
%              Number of equality atoms :   24 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(subsumption_resolution,[],[f17,f169])).

fof(f169,plain,(
    ! [X12] : k7_relat_1(k5_relat_1(sK1,sK2),X12) = k5_relat_1(k7_relat_1(sK1,X12),sK2) ),
    inference(forward_demodulation,[],[f165,f105])).

fof(f105,plain,(
    ! [X2] : k5_relat_1(k6_relat_1(X2),k5_relat_1(sK1,sK2)) = k5_relat_1(k7_relat_1(sK1,X2),sK2) ),
    inference(forward_demodulation,[],[f99,f24])).

fof(f24,plain,(
    ! [X5] : k7_relat_1(sK1,X5) = k5_relat_1(k6_relat_1(X5),sK1) ),
    inference(resolution,[],[f20,f15])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k7_relat_1(k5_relat_1(sK1,sK2),sK0) != k5_relat_1(k7_relat_1(sK1,sK0),sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_relat_1(k5_relat_1(X1,X2),X0) != k5_relat_1(k7_relat_1(X1,X0),X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(k5_relat_1(sK1,X2),sK0) != k5_relat_1(k7_relat_1(sK1,sK0),X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( k7_relat_1(k5_relat_1(sK1,X2),sK0) != k5_relat_1(k7_relat_1(sK1,sK0),X2)
        & v1_relat_1(X2) )
   => ( k7_relat_1(k5_relat_1(sK1,sK2),sK0) != k5_relat_1(k7_relat_1(sK1,sK0),sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) != k5_relat_1(k7_relat_1(X1,X0),X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f99,plain,(
    ! [X2] : k5_relat_1(k5_relat_1(k6_relat_1(X2),sK1),sK2) = k5_relat_1(k6_relat_1(X2),k5_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f44,f18])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f44,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X5,sK1),sK2) = k5_relat_1(X5,k5_relat_1(sK1,sK2)) ) ),
    inference(resolution,[],[f29,f15])).

fof(f29,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X10)
      | k5_relat_1(k5_relat_1(X9,X10),sK2) = k5_relat_1(X9,k5_relat_1(X10,sK2))
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f19,f16])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f165,plain,(
    ! [X12] : k7_relat_1(k5_relat_1(sK1,sK2),X12) = k5_relat_1(k6_relat_1(X12),k5_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f50,f15])).

fof(f50,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X9)
      | k7_relat_1(k5_relat_1(X9,sK2),X10) = k5_relat_1(k6_relat_1(X10),k5_relat_1(X9,sK2)) ) ),
    inference(resolution,[],[f22,f16])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k6_relat_1(X2),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f17,plain,(
    k7_relat_1(k5_relat_1(sK1,sK2),sK0) != k5_relat_1(k7_relat_1(sK1,sK0),sK2) ),
    inference(cnf_transformation,[],[f14])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (7625)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.42  % (7622)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (7617)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.42  % (7616)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.45  % (7621)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.45  % (7619)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.45  % (7620)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.46  % (7623)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.46  % (7624)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.46  % (7626)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.46  % (7615)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.47  % (7618)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.48  % (7626)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f17,f169])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ( ! [X12] : (k7_relat_1(k5_relat_1(sK1,sK2),X12) = k5_relat_1(k7_relat_1(sK1,X12),sK2)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f165,f105])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ( ! [X2] : (k5_relat_1(k6_relat_1(X2),k5_relat_1(sK1,sK2)) = k5_relat_1(k7_relat_1(sK1,X2),sK2)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f99,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X5] : (k7_relat_1(sK1,X5) = k5_relat_1(k6_relat_1(X5),sK1)) )),
% 0.20/0.48    inference(resolution,[],[f20,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    (k7_relat_1(k5_relat_1(sK1,sK2),sK0) != k5_relat_1(k7_relat_1(sK1,sK0),sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) != k5_relat_1(k7_relat_1(X1,X0),X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(k5_relat_1(sK1,X2),sK0) != k5_relat_1(k7_relat_1(sK1,sK0),X2) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X2] : (k7_relat_1(k5_relat_1(sK1,X2),sK0) != k5_relat_1(k7_relat_1(sK1,sK0),X2) & v1_relat_1(X2)) => (k7_relat_1(k5_relat_1(sK1,sK2),sK0) != k5_relat_1(k7_relat_1(sK1,sK0),sK2) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) != k5_relat_1(k7_relat_1(X1,X0),X2) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ( ! [X2] : (k5_relat_1(k5_relat_1(k6_relat_1(X2),sK1),sK2) = k5_relat_1(k6_relat_1(X2),k5_relat_1(sK1,sK2))) )),
% 0.20/0.48    inference(resolution,[],[f44,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X5] : (~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X5,sK1),sK2) = k5_relat_1(X5,k5_relat_1(sK1,sK2))) )),
% 0.20/0.48    inference(resolution,[],[f29,f15])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X10,X9] : (~v1_relat_1(X10) | k5_relat_1(k5_relat_1(X9,X10),sK2) = k5_relat_1(X9,k5_relat_1(X10,sK2)) | ~v1_relat_1(X9)) )),
% 0.20/0.48    inference(resolution,[],[f19,f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    ( ! [X12] : (k7_relat_1(k5_relat_1(sK1,sK2),X12) = k5_relat_1(k6_relat_1(X12),k5_relat_1(sK1,sK2))) )),
% 0.20/0.48    inference(resolution,[],[f50,f15])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X10,X9] : (~v1_relat_1(X9) | k7_relat_1(k5_relat_1(X9,sK2),X10) = k5_relat_1(k6_relat_1(X10),k5_relat_1(X9,sK2))) )),
% 0.20/0.48    inference(resolution,[],[f22,f16])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k6_relat_1(X2),k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(resolution,[],[f20,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    k7_relat_1(k5_relat_1(sK1,sK2),sK0) != k5_relat_1(k7_relat_1(sK1,sK0),sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (7626)------------------------------
% 0.20/0.48  % (7626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (7626)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (7626)Memory used [KB]: 10874
% 0.20/0.48  % (7626)Time elapsed: 0.070 s
% 0.20/0.48  % (7626)------------------------------
% 0.20/0.48  % (7626)------------------------------
% 0.20/0.49  % (7614)Success in time 0.131 s
%------------------------------------------------------------------------------
