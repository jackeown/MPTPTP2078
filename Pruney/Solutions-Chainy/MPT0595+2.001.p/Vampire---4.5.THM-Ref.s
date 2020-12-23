%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   18 (  43 expanded)
%              Number of leaves         :    2 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 ( 153 expanded)
%              Number of equality atoms :   18 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f9])).

fof(f9,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( k2_relat_1(X0) = k2_relat_1(X1)
                 => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

fof(f28,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(superposition,[],[f19,f18])).

fof(f18,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0)) ),
    inference(resolution,[],[f13,f11])).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,sK2)) = k9_relat_1(sK2,k2_relat_1(X0)) ) ),
    inference(resolution,[],[f12,f7])).

fof(f7,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f19,plain,(
    k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f17,f8])).

fof(f8,plain,(
    k2_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f17,plain,(
    k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1)) ),
    inference(resolution,[],[f13,f10])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (32165)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.41  % (32168)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.41  % (32170)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (32168)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(subsumption_resolution,[],[f28,f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2))),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (? [X2] : (k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2)) & k2_relat_1(X0) = k2_relat_1(X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.41    inference(flattening,[],[f4])).
% 0.20/0.41  fof(f4,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (? [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2)) & k2_relat_1(X0) = k2_relat_1(X1)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,negated_conjecture,(
% 0.20/0.41    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.20/0.41    inference(negated_conjecture,[],[f2])).
% 0.20/0.41  fof(f2,conjecture,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    k2_relat_1(k5_relat_1(sK0,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2))),
% 0.20/0.41    inference(superposition,[],[f19,f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    k2_relat_1(k5_relat_1(sK0,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0))),
% 0.20/0.41    inference(resolution,[],[f13,f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    v1_relat_1(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,sK2)) = k9_relat_1(sK2,k2_relat_1(X0))) )),
% 0.20/0.41    inference(resolution,[],[f12,f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    v1_relat_1(sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,plain,(
% 0.20/0.41    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0))),
% 0.20/0.41    inference(forward_demodulation,[],[f17,f8])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    k2_relat_1(sK0) = k2_relat_1(sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1))),
% 0.20/0.41    inference(resolution,[],[f13,f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    v1_relat_1(sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f5])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (32168)------------------------------
% 0.20/0.41  % (32168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (32168)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (32168)Memory used [KB]: 10490
% 0.20/0.41  % (32168)Time elapsed: 0.028 s
% 0.20/0.41  % (32168)------------------------------
% 0.20/0.41  % (32168)------------------------------
% 0.20/0.41  % (32164)Success in time 0.06 s
%------------------------------------------------------------------------------
