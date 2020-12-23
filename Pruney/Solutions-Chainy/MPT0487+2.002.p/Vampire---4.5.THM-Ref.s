%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:18 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  67 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 311 expanded)
%              Number of equality atoms :   35 ( 131 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(subsumption_resolution,[],[f67,f18])).

fof(f18,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

% (17995)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                    & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                    & r1_tarski(k2_relat_1(X1),X0) )
                 => X1 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & r1_tarski(k2_relat_1(X1),X0) )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_relat_1)).

fof(f67,plain,(
    sK1 = sK3 ),
    inference(forward_demodulation,[],[f66,f30])).

% (17985)Refutation not found, incomplete strategy% (17985)------------------------------
% (17985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17985)Termination reason: Refutation not found, incomplete strategy

% (17985)Memory used [KB]: 6140
% (17985)Time elapsed: 0.124 s
% (17985)------------------------------
% (17985)------------------------------
fof(f30,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f20,f15,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f15,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    sK3 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f65,f37])).

fof(f37,plain,(
    sK3 = k5_relat_1(k5_relat_1(sK1,sK2),sK3) ),
    inference(forward_demodulation,[],[f34,f16])).

fof(f16,plain,(
    k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) ),
    inference(unit_resulting_resolution,[],[f14,f27,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f27,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f14,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    k5_relat_1(sK1,k6_relat_1(sK0)) = k5_relat_1(k5_relat_1(sK1,sK2),sK3) ),
    inference(forward_demodulation,[],[f53,f17])).

fof(f17,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    k5_relat_1(k5_relat_1(sK1,sK2),sK3) = k5_relat_1(sK1,k5_relat_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f14,f20,f19,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

% (18004)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.55  % (17985)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.55  % (17991)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.55  % (17988)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.55  % (17987)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.55  % (17999)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.55  % (17986)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.55  % (17983)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.55  % (17984)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.55  % (17996)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.55  % (17987)Refutation found. Thanks to Tanya!
% 0.19/0.55  % SZS status Theorem for theBenchmark
% 0.19/0.56  % (18001)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.56  % (18003)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.56  % SZS output start Proof for theBenchmark
% 0.19/0.56  fof(f68,plain,(
% 0.19/0.56    $false),
% 0.19/0.56    inference(subsumption_resolution,[],[f67,f18])).
% 0.19/0.56  fof(f18,plain,(
% 0.19/0.56    sK1 != sK3),
% 0.19/0.56    inference(cnf_transformation,[],[f8])).
% 0.19/0.56  fof(f8,plain,(
% 0.19/0.56    ? [X0,X1] : (? [X2] : (? [X3] : (X1 != X3 & k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.19/0.56    inference(flattening,[],[f7])).
% 0.19/0.56  % (17995)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.56  fof(f7,plain,(
% 0.19/0.56    ? [X0,X1] : (? [X2] : (? [X3] : ((X1 != X3 & (k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0))) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.19/0.56    inference(ennf_transformation,[],[f6])).
% 0.19/0.56  fof(f6,negated_conjecture,(
% 0.19/0.56    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 0.19/0.56    inference(negated_conjecture,[],[f5])).
% 0.19/0.56  fof(f5,conjecture,(
% 0.19/0.56    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_relat_1)).
% 0.19/0.56  fof(f67,plain,(
% 0.19/0.56    sK1 = sK3),
% 0.19/0.56    inference(forward_demodulation,[],[f66,f30])).
% 0.19/0.56  % (17985)Refutation not found, incomplete strategy% (17985)------------------------------
% 0.19/0.56  % (17985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (17985)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (17985)Memory used [KB]: 6140
% 0.19/0.56  % (17985)Time elapsed: 0.124 s
% 0.19/0.56  % (17985)------------------------------
% 0.19/0.56  % (17985)------------------------------
% 0.19/0.56  fof(f30,plain,(
% 0.19/0.56    sK1 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f20,f15,f22])).
% 0.19/0.56  fof(f22,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.19/0.56    inference(cnf_transformation,[],[f11])).
% 0.19/0.56  fof(f11,plain,(
% 0.19/0.56    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.56    inference(flattening,[],[f10])).
% 0.19/0.56  fof(f10,plain,(
% 0.19/0.56    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.56    inference(ennf_transformation,[],[f4])).
% 0.19/0.56  fof(f4,axiom,(
% 0.19/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.19/0.56  fof(f15,plain,(
% 0.19/0.56    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.19/0.56    inference(cnf_transformation,[],[f8])).
% 0.19/0.56  fof(f20,plain,(
% 0.19/0.56    v1_relat_1(sK1)),
% 0.19/0.56    inference(cnf_transformation,[],[f8])).
% 0.19/0.56  fof(f66,plain,(
% 0.19/0.56    sK3 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.19/0.56    inference(forward_demodulation,[],[f65,f37])).
% 0.19/0.56  fof(f37,plain,(
% 0.19/0.56    sK3 = k5_relat_1(k5_relat_1(sK1,sK2),sK3)),
% 0.19/0.56    inference(forward_demodulation,[],[f34,f16])).
% 0.19/0.56  fof(f16,plain,(
% 0.19/0.56    k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))),
% 0.19/0.56    inference(cnf_transformation,[],[f8])).
% 0.19/0.56  fof(f34,plain,(
% 0.19/0.56    sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f14,f27,f23])).
% 0.19/0.56  fof(f23,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.19/0.56    inference(cnf_transformation,[],[f13])).
% 0.19/0.56  fof(f13,plain,(
% 0.19/0.56    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.56    inference(flattening,[],[f12])).
% 0.19/0.56  fof(f12,plain,(
% 0.19/0.56    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.56    inference(ennf_transformation,[],[f3])).
% 0.19/0.56  fof(f3,axiom,(
% 0.19/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.19/0.56  fof(f27,plain,(
% 0.19/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.56    inference(equality_resolution,[],[f25])).
% 0.19/0.56  fof(f25,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.56    inference(cnf_transformation,[],[f1])).
% 0.19/0.56  fof(f1,axiom,(
% 0.19/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.56  fof(f14,plain,(
% 0.19/0.56    v1_relat_1(sK3)),
% 0.19/0.56    inference(cnf_transformation,[],[f8])).
% 0.19/0.56  fof(f65,plain,(
% 0.19/0.56    k5_relat_1(sK1,k6_relat_1(sK0)) = k5_relat_1(k5_relat_1(sK1,sK2),sK3)),
% 0.19/0.56    inference(forward_demodulation,[],[f53,f17])).
% 0.19/0.56  fof(f17,plain,(
% 0.19/0.56    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.19/0.56    inference(cnf_transformation,[],[f8])).
% 0.19/0.56  fof(f53,plain,(
% 0.19/0.56    k5_relat_1(k5_relat_1(sK1,sK2),sK3) = k5_relat_1(sK1,k5_relat_1(sK2,sK3))),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f14,f20,f19,f21])).
% 0.19/0.56  fof(f21,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f9])).
% 0.19/0.56  fof(f9,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.56    inference(ennf_transformation,[],[f2])).
% 0.19/0.56  fof(f2,axiom,(
% 0.19/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.19/0.56  % (18004)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.56  fof(f19,plain,(
% 0.19/0.56    v1_relat_1(sK2)),
% 0.19/0.56    inference(cnf_transformation,[],[f8])).
% 0.19/0.56  % SZS output end Proof for theBenchmark
% 0.19/0.56  % (17987)------------------------------
% 0.19/0.56  % (17987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (17987)Termination reason: Refutation
% 0.19/0.56  
% 0.19/0.56  % (17987)Memory used [KB]: 1663
% 0.19/0.56  % (17987)Time elapsed: 0.127 s
% 0.19/0.56  % (17987)------------------------------
% 0.19/0.56  % (17987)------------------------------
% 0.19/0.56  % (17992)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.56  % (17979)Success in time 0.202 s
%------------------------------------------------------------------------------
