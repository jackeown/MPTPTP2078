%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:56 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 101 expanded)
%              Number of leaves         :    7 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 468 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(subsumption_resolution,[],[f103,f22])).

fof(f22,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f103,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(forward_demodulation,[],[f102,f38])).

fof(f38,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f18,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,(
    r1_tarski(k2_relat_1(k7_relat_1(sK2,sK0)),k9_relat_1(sK3,sK1)) ),
    inference(forward_demodulation,[],[f100,f39])).

fof(f39,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f19,f26])).

fof(f19,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f100,plain,(
    r1_tarski(k2_relat_1(k7_relat_1(sK2,sK0)),k2_relat_1(k7_relat_1(sK3,sK1))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f91,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f91,plain,(
    r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f18,f19,f20,f21,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f19,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f18,f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n009.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 20:18:11 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.18/0.37  % (5676)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.18/0.37  % (5677)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.18/0.37  % (5670)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.18/0.37  % (5670)Refutation found. Thanks to Tanya!
% 0.18/0.37  % SZS status Theorem for theBenchmark
% 0.18/0.37  % SZS output start Proof for theBenchmark
% 0.18/0.37  fof(f104,plain,(
% 0.18/0.37    $false),
% 0.18/0.37    inference(subsumption_resolution,[],[f103,f22])).
% 0.18/0.37  fof(f22,plain,(
% 0.18/0.37    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 0.18/0.37    inference(cnf_transformation,[],[f17])).
% 0.18/0.37  fof(f17,plain,(
% 0.18/0.37    (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.18/0.37    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15])).
% 0.18/0.38  fof(f15,plain,(
% 0.18/0.38    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.18/0.38    introduced(choice_axiom,[])).
% 0.18/0.38  fof(f16,plain,(
% 0.18/0.38    ? [X3] : (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.18/0.38    introduced(choice_axiom,[])).
% 0.18/0.38  fof(f8,plain,(
% 0.18/0.38    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.18/0.38    inference(flattening,[],[f7])).
% 0.18/0.38  fof(f7,plain,(
% 0.18/0.38    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.18/0.38    inference(ennf_transformation,[],[f6])).
% 0.18/0.38  fof(f6,negated_conjecture,(
% 0.18/0.38    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.18/0.38    inference(negated_conjecture,[],[f5])).
% 0.18/0.38  fof(f5,conjecture,(
% 0.18/0.38    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.18/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).
% 0.18/0.38  fof(f103,plain,(
% 0.18/0.38    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 0.18/0.38    inference(forward_demodulation,[],[f102,f38])).
% 0.18/0.38  fof(f38,plain,(
% 0.18/0.38    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.18/0.38    inference(unit_resulting_resolution,[],[f18,f26])).
% 0.18/0.38  fof(f26,plain,(
% 0.18/0.38    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.18/0.38    inference(cnf_transformation,[],[f12])).
% 0.18/0.38  fof(f12,plain,(
% 0.18/0.38    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.38    inference(ennf_transformation,[],[f3])).
% 0.18/0.38  fof(f3,axiom,(
% 0.18/0.38    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.18/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.18/0.38  fof(f18,plain,(
% 0.18/0.38    v1_relat_1(sK2)),
% 0.18/0.38    inference(cnf_transformation,[],[f17])).
% 0.18/0.38  fof(f102,plain,(
% 0.18/0.38    r1_tarski(k2_relat_1(k7_relat_1(sK2,sK0)),k9_relat_1(sK3,sK1))),
% 0.18/0.38    inference(forward_demodulation,[],[f100,f39])).
% 0.18/0.38  fof(f39,plain,(
% 0.18/0.38    ( ! [X0] : (k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0)) )),
% 0.18/0.38    inference(unit_resulting_resolution,[],[f19,f26])).
% 0.18/0.38  fof(f19,plain,(
% 0.18/0.38    v1_relat_1(sK3)),
% 0.18/0.38    inference(cnf_transformation,[],[f17])).
% 0.18/0.38  fof(f100,plain,(
% 0.18/0.38    r1_tarski(k2_relat_1(k7_relat_1(sK2,sK0)),k2_relat_1(k7_relat_1(sK3,sK1)))),
% 0.18/0.38    inference(unit_resulting_resolution,[],[f28,f29,f91,f24])).
% 0.18/0.38  fof(f24,plain,(
% 0.18/0.38    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.18/0.38    inference(cnf_transformation,[],[f10])).
% 0.18/0.38  fof(f10,plain,(
% 0.18/0.38    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.38    inference(flattening,[],[f9])).
% 0.18/0.38  fof(f9,plain,(
% 0.18/0.38    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.38    inference(ennf_transformation,[],[f4])).
% 0.18/0.38  fof(f4,axiom,(
% 0.18/0.38    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.18/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.18/0.38  fof(f91,plain,(
% 0.18/0.38    r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.18/0.38    inference(unit_resulting_resolution,[],[f18,f19,f20,f21,f27])).
% 0.18/0.38  fof(f27,plain,(
% 0.18/0.38    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 0.18/0.38    inference(cnf_transformation,[],[f14])).
% 0.18/0.38  fof(f14,plain,(
% 0.18/0.38    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 0.18/0.38    inference(flattening,[],[f13])).
% 0.18/0.38  fof(f13,plain,(
% 0.18/0.38    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 0.18/0.38    inference(ennf_transformation,[],[f2])).
% 0.18/0.38  fof(f2,axiom,(
% 0.18/0.38    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.18/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).
% 0.18/0.38  fof(f21,plain,(
% 0.18/0.38    r1_tarski(sK0,sK1)),
% 0.18/0.38    inference(cnf_transformation,[],[f17])).
% 0.18/0.38  fof(f20,plain,(
% 0.18/0.38    r1_tarski(sK2,sK3)),
% 0.18/0.38    inference(cnf_transformation,[],[f17])).
% 0.18/0.38  fof(f29,plain,(
% 0.18/0.38    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 0.18/0.38    inference(unit_resulting_resolution,[],[f19,f25])).
% 0.18/0.38  fof(f25,plain,(
% 0.18/0.38    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.18/0.38    inference(cnf_transformation,[],[f11])).
% 0.18/0.38  fof(f11,plain,(
% 0.18/0.38    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.18/0.38    inference(ennf_transformation,[],[f1])).
% 0.18/0.38  fof(f1,axiom,(
% 0.18/0.38    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.18/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.18/0.38  fof(f28,plain,(
% 0.18/0.38    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.18/0.38    inference(unit_resulting_resolution,[],[f18,f25])).
% 0.18/0.38  % SZS output end Proof for theBenchmark
% 0.18/0.38  % (5670)------------------------------
% 0.18/0.38  % (5670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.38  % (5670)Termination reason: Refutation
% 0.18/0.38  
% 0.18/0.38  % (5670)Memory used [KB]: 6140
% 0.18/0.38  % (5670)Time elapsed: 0.004 s
% 0.18/0.38  % (5670)------------------------------
% 0.18/0.38  % (5670)------------------------------
% 0.18/0.38  % (5661)Success in time 0.05 s
%------------------------------------------------------------------------------
