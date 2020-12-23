%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:23 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   23 (  49 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 151 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f14,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),X2),k5_relat_1(sK1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),X2),k5_relat_1(sK1,X2))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_relat_1)).

fof(f28,plain,(
    ~ r1_tarski(k7_relat_1(sK1,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f15,f14,f20,f16,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
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
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

fof(f16,plain,(
    ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f14,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n011.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 14:37:57 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.23/0.46  % (12909)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.23/0.47  % (12910)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.23/0.47  % (12901)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.23/0.47  % (12909)Refutation found. Thanks to Tanya!
% 0.23/0.47  % SZS status Theorem for theBenchmark
% 0.23/0.47  % SZS output start Proof for theBenchmark
% 0.23/0.47  fof(f29,plain,(
% 0.23/0.47    $false),
% 0.23/0.47    inference(subsumption_resolution,[],[f28,f22])).
% 0.23/0.47  fof(f22,plain,(
% 0.23/0.47    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),sK1)) )),
% 0.23/0.47    inference(unit_resulting_resolution,[],[f14,f19])).
% 0.23/0.47  fof(f19,plain,(
% 0.23/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 0.23/0.47    inference(cnf_transformation,[],[f10])).
% 0.23/0.47  fof(f10,plain,(
% 0.23/0.47    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.47    inference(ennf_transformation,[],[f3])).
% 0.23/0.47  fof(f3,axiom,(
% 0.23/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.23/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.23/0.47  fof(f14,plain,(
% 0.23/0.47    v1_relat_1(sK1)),
% 0.23/0.47    inference(cnf_transformation,[],[f13])).
% 0.23/0.47  fof(f13,plain,(
% 0.23/0.47    (~r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.23/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11])).
% 0.23/0.47  fof(f11,plain,(
% 0.23/0.47    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),X2),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.23/0.47    introduced(choice_axiom,[])).
% 0.23/0.47  fof(f12,plain,(
% 0.23/0.47    ? [X2] : (~r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),X2),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2))),
% 0.23/0.47    introduced(choice_axiom,[])).
% 0.23/0.47  fof(f6,plain,(
% 0.23/0.47    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.23/0.47    inference(ennf_transformation,[],[f5])).
% 0.23/0.47  fof(f5,negated_conjecture,(
% 0.23/0.47    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))))),
% 0.23/0.47    inference(negated_conjecture,[],[f4])).
% 0.23/0.47  fof(f4,conjecture,(
% 0.23/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))))),
% 0.23/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_relat_1)).
% 0.23/0.47  fof(f28,plain,(
% 0.23/0.47    ~r1_tarski(k7_relat_1(sK1,sK0),sK1)),
% 0.23/0.47    inference(unit_resulting_resolution,[],[f15,f14,f20,f16,f17])).
% 0.23/0.47  fof(f17,plain,(
% 0.23/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.47    inference(cnf_transformation,[],[f8])).
% 0.23/0.47  fof(f8,plain,(
% 0.23/0.47    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.47    inference(flattening,[],[f7])).
% 0.23/0.47  fof(f7,plain,(
% 0.23/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.47    inference(ennf_transformation,[],[f2])).
% 0.23/0.47  fof(f2,axiom,(
% 0.23/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))))))),
% 0.23/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).
% 0.23/0.47  fof(f16,plain,(
% 0.23/0.47    ~r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2))),
% 0.23/0.47    inference(cnf_transformation,[],[f13])).
% 0.23/0.47  fof(f20,plain,(
% 0.23/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.23/0.47    inference(unit_resulting_resolution,[],[f14,f18])).
% 0.23/0.47  fof(f18,plain,(
% 0.23/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.23/0.47    inference(cnf_transformation,[],[f9])).
% 0.23/0.47  fof(f9,plain,(
% 0.23/0.47    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.23/0.47    inference(ennf_transformation,[],[f1])).
% 0.23/0.47  fof(f1,axiom,(
% 0.23/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.23/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.23/0.47  fof(f15,plain,(
% 0.23/0.47    v1_relat_1(sK2)),
% 0.23/0.47    inference(cnf_transformation,[],[f13])).
% 0.23/0.47  % SZS output end Proof for theBenchmark
% 0.23/0.47  % (12909)------------------------------
% 0.23/0.47  % (12909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.47  % (12909)Termination reason: Refutation
% 0.23/0.47  
% 0.23/0.47  % (12909)Memory used [KB]: 5373
% 0.23/0.47  % (12909)Time elapsed: 0.049 s
% 0.23/0.47  % (12909)------------------------------
% 0.23/0.47  % (12909)------------------------------
% 0.23/0.47  % (12894)Success in time 0.098 s
%------------------------------------------------------------------------------
