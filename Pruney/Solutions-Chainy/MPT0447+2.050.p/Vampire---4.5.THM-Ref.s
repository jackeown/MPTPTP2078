%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 126 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 454 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f679,plain,(
    $false ),
    inference(subsumption_resolution,[],[f678,f26])).

fof(f26,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f678,plain,(
    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f669,f75])).

fof(f75,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f23,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f669,plain,(
    r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f554,f653,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f653,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f105,f466])).

fof(f466,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK1),X1)
      | r1_tarski(k1_relat_1(sK0),X1) ) ),
    inference(superposition,[],[f33,f428])).

fof(f428,plain,(
    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f423,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f423,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f105,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f30,f76])).

fof(f76,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f24,f27])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f554,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f548,f104])).

fof(f104,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK1))
      | r1_tarski(X2,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f32,f76])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f548,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:54:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (27987)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.43  % (27978)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (27979)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.45  % (27979)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % (27977)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.45  % (27983)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.46  % (27982)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f679,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(subsumption_resolution,[],[f678,f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f21,f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.46    inference(flattening,[],[f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,negated_conjecture,(
% 0.22/0.46    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.22/0.46    inference(negated_conjecture,[],[f8])).
% 0.22/0.46  fof(f8,conjecture,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 0.22/0.46  fof(f678,plain,(
% 0.22/0.46    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.22/0.46    inference(forward_demodulation,[],[f669,f75])).
% 0.22/0.46  fof(f75,plain,(
% 0.22/0.46    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f23,f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    v1_relat_1(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f669,plain,(
% 0.22/0.46    r1_tarski(k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)),k3_relat_1(sK1))),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f554,f653,f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(flattening,[],[f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.22/0.46  fof(f653,plain,(
% 0.22/0.46    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f105,f466])).
% 0.22/0.46  fof(f466,plain,(
% 0.22/0.46    ( ! [X1] : (~r1_tarski(k1_relat_1(sK1),X1) | r1_tarski(k1_relat_1(sK0),X1)) )),
% 0.22/0.46    inference(superposition,[],[f33,f428])).
% 0.22/0.46  fof(f428,plain,(
% 0.22/0.46    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f423,f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.46  fof(f423,plain,(
% 0.22/0.46    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f23,f24,f25,f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(flattening,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    r1_tarski(sK0,sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    v1_relat_1(sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f22])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.46  fof(f105,plain,(
% 0.22/0.46    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 0.22/0.46    inference(superposition,[],[f30,f76])).
% 0.22/0.46  fof(f76,plain,(
% 0.22/0.46    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f24,f27])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.46  fof(f554,plain,(
% 0.22/0.46    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f548,f104])).
% 0.22/0.46  fof(f104,plain,(
% 0.22/0.46    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK1)) | r1_tarski(X2,k3_relat_1(sK1))) )),
% 0.22/0.46    inference(superposition,[],[f32,f76])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.46  fof(f548,plain,(
% 0.22/0.46    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f23,f24,f25,f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (27979)------------------------------
% 0.22/0.46  % (27979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (27979)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (27979)Memory used [KB]: 6524
% 0.22/0.46  % (27979)Time elapsed: 0.021 s
% 0.22/0.46  % (27979)------------------------------
% 0.22/0.46  % (27979)------------------------------
% 0.22/0.46  % (27984)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.46  % (27976)Success in time 0.103 s
%------------------------------------------------------------------------------
