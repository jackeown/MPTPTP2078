%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  58 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   84 ( 300 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f14,f15,f17,f22,f18,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(X2,k7_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

% (2430)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).

fof(f18,plain,(
    ~ r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    & r1_tarski(sK2,sK1)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f11,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
          & r1_tarski(X2,sK1)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
        & r1_tarski(X2,sK1)
        & v4_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
      & r1_tarski(sK2,sK1)
      & v4_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( r1_tarski(X2,X1)
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( r1_tarski(X2,X1)
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t210_relat_1)).

fof(f22,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f15,f16,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f16,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (2417)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.47  % (2431)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.47  % (2422)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.47  % (2431)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f14,f15,f17,f22,f18,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(X2,k7_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k7_relat_1(X1,X0)) | ~r1_tarski(X2,X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f8])).
% 0.20/0.47  % (2430)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k7_relat_1(X1,X0)) | (~r1_tarski(X2,X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ~r1_tarski(sK2,k7_relat_1(sK1,sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f11,f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) => (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f5])).
% 0.20/0.47  fof(f5,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1)) & (v4_relat_1(X2,X0) & v1_relat_1(X2))) & v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => (r1_tarski(X2,X1) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f3])).
% 0.20/0.47  fof(f3,conjecture,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => (r1_tarski(X2,X1) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t210_relat_1)).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f15,f16,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    v4_relat_1(sK2,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    r1_tarski(sK2,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (2431)------------------------------
% 0.20/0.47  % (2431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (2431)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (2431)Memory used [KB]: 5373
% 0.20/0.47  % (2431)Time elapsed: 0.005 s
% 0.20/0.47  % (2431)------------------------------
% 0.20/0.47  % (2431)------------------------------
% 0.20/0.48  % (2413)Success in time 0.124 s
%------------------------------------------------------------------------------
