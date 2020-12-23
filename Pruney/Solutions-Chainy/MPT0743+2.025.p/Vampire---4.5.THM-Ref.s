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
% DateTime   : Thu Dec  3 12:55:26 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 233 expanded)
%              Number of leaves         :    9 (  52 expanded)
%              Depth                    :   21
%              Number of atoms          :  130 ( 648 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(subsumption_resolution,[],[f168,f24])).

fof(f24,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f168,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(forward_demodulation,[],[f167,f129])).

fof(f129,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f126,f98])).

fof(f98,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f95,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f95,plain,(
    r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f90,f24])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_ordinal1(sK0))
      | r2_hidden(X0,sK1)
      | r2_hidden(sK0,sK1) ) ),
    inference(resolution,[],[f89,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f89,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f88,f23])).

fof(f23,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f88,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f65,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f65,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | r1_tarski(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f62,f20])).

fof(f20,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK1)
      | r1_tarski(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f126,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f123,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | X0 = X1
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f123,plain,(
    r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f122,f23])).

fof(f122,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f103,f25])).

fof(f103,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f101,f22])).

fof(f101,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f96,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f96,plain,(
    ~ r1_ordinal1(k1_ordinal1(sK0),sK1) ),
    inference(resolution,[],[f95,f21])).

fof(f21,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_ordinal1(k1_ordinal1(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f167,plain,(
    ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f139,f51])).

fof(f51,plain,(
    ! [X2] : ~ r2_hidden(X2,X2) ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f49,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f32,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f139,plain,
    ( r2_hidden(sK0,sK0)
    | ~ r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(backward_demodulation,[],[f91,f129])).

fof(f91,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f89,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:38:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.36/0.55  % (10396)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.55  % (10389)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.55  % (10404)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.55  % (10388)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.56  % (10405)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.56  % (10388)Refutation found. Thanks to Tanya!
% 1.36/0.56  % SZS status Theorem for theBenchmark
% 1.36/0.56  % SZS output start Proof for theBenchmark
% 1.36/0.56  fof(f169,plain,(
% 1.36/0.56    $false),
% 1.36/0.56    inference(subsumption_resolution,[],[f168,f24])).
% 1.36/0.56  fof(f24,plain,(
% 1.36/0.56    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f4])).
% 1.36/0.56  fof(f4,axiom,(
% 1.36/0.56    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.36/0.56  fof(f168,plain,(
% 1.36/0.56    ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 1.36/0.56    inference(forward_demodulation,[],[f167,f129])).
% 1.36/0.56  fof(f129,plain,(
% 1.36/0.56    sK0 = sK1),
% 1.36/0.56    inference(subsumption_resolution,[],[f126,f98])).
% 1.36/0.56  fof(f98,plain,(
% 1.36/0.56    ~r2_hidden(sK1,sK0)),
% 1.36/0.56    inference(resolution,[],[f95,f27])).
% 1.36/0.56  fof(f27,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f15])).
% 1.36/0.56  fof(f15,plain,(
% 1.36/0.56    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.36/0.56    inference(ennf_transformation,[],[f1])).
% 1.36/0.56  fof(f1,axiom,(
% 1.36/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.36/0.56  fof(f95,plain,(
% 1.36/0.56    r2_hidden(sK0,sK1)),
% 1.36/0.56    inference(duplicate_literal_removal,[],[f92])).
% 1.36/0.56  fof(f92,plain,(
% 1.36/0.56    r2_hidden(sK0,sK1) | r2_hidden(sK0,sK1)),
% 1.36/0.56    inference(resolution,[],[f90,f24])).
% 1.36/0.56  fof(f90,plain,(
% 1.36/0.56    ( ! [X0] : (~r2_hidden(X0,k1_ordinal1(sK0)) | r2_hidden(X0,sK1) | r2_hidden(sK0,sK1)) )),
% 1.36/0.56    inference(resolution,[],[f89,f30])).
% 1.36/0.56  fof(f30,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f18])).
% 1.36/0.56  fof(f18,plain,(
% 1.36/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f2])).
% 1.36/0.56  fof(f2,axiom,(
% 1.36/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.56  fof(f89,plain,(
% 1.36/0.56    r1_tarski(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.36/0.56    inference(subsumption_resolution,[],[f88,f23])).
% 1.36/0.56  fof(f23,plain,(
% 1.36/0.56    v3_ordinal1(sK0)),
% 1.36/0.56    inference(cnf_transformation,[],[f11])).
% 1.36/0.56  fof(f11,plain,(
% 1.36/0.56    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.36/0.56    inference(ennf_transformation,[],[f10])).
% 1.36/0.56  fof(f10,negated_conjecture,(
% 1.36/0.56    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.36/0.56    inference(negated_conjecture,[],[f9])).
% 1.36/0.56  fof(f9,conjecture,(
% 1.36/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 1.36/0.56  fof(f88,plain,(
% 1.36/0.56    r1_tarski(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 1.36/0.56    inference(resolution,[],[f65,f25])).
% 1.36/0.56  fof(f25,plain,(
% 1.36/0.56    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f12])).
% 1.36/0.56  fof(f12,plain,(
% 1.36/0.56    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.36/0.56    inference(ennf_transformation,[],[f7])).
% 1.36/0.56  fof(f7,axiom,(
% 1.36/0.56    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 1.36/0.56  fof(f65,plain,(
% 1.36/0.56    ~v3_ordinal1(k1_ordinal1(sK0)) | r1_tarski(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.36/0.56    inference(resolution,[],[f62,f20])).
% 1.36/0.56  fof(f20,plain,(
% 1.36/0.56    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.36/0.56    inference(cnf_transformation,[],[f11])).
% 1.36/0.56  fof(f62,plain,(
% 1.36/0.56    ( ! [X0] : (~r1_ordinal1(X0,sK1) | r1_tarski(X0,sK1) | ~v3_ordinal1(X0)) )),
% 1.36/0.56    inference(resolution,[],[f29,f22])).
% 1.36/0.56  fof(f22,plain,(
% 1.36/0.56    v3_ordinal1(sK1)),
% 1.36/0.56    inference(cnf_transformation,[],[f11])).
% 1.36/0.56  fof(f29,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f17])).
% 1.36/0.56  fof(f17,plain,(
% 1.36/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.36/0.56    inference(flattening,[],[f16])).
% 1.36/0.56  fof(f16,plain,(
% 1.36/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.36/0.56    inference(ennf_transformation,[],[f3])).
% 1.36/0.56  fof(f3,axiom,(
% 1.36/0.56    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.36/0.56  fof(f126,plain,(
% 1.36/0.56    sK0 = sK1 | r2_hidden(sK1,sK0)),
% 1.36/0.56    inference(resolution,[],[f123,f33])).
% 1.36/0.56  fof(f33,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | X0 = X1 | r2_hidden(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f5])).
% 1.36/0.56  fof(f5,axiom,(
% 1.36/0.56    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.36/0.56  fof(f123,plain,(
% 1.36/0.56    r2_hidden(sK1,k1_ordinal1(sK0))),
% 1.36/0.56    inference(subsumption_resolution,[],[f122,f23])).
% 1.36/0.56  fof(f122,plain,(
% 1.36/0.56    r2_hidden(sK1,k1_ordinal1(sK0)) | ~v3_ordinal1(sK0)),
% 1.36/0.56    inference(resolution,[],[f103,f25])).
% 1.36/0.56  fof(f103,plain,(
% 1.36/0.56    ~v3_ordinal1(k1_ordinal1(sK0)) | r2_hidden(sK1,k1_ordinal1(sK0))),
% 1.36/0.56    inference(subsumption_resolution,[],[f101,f22])).
% 1.36/0.56  fof(f101,plain,(
% 1.36/0.56    ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | r2_hidden(sK1,k1_ordinal1(sK0))),
% 1.36/0.56    inference(resolution,[],[f96,f26])).
% 1.36/0.56  fof(f26,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f14])).
% 1.36/0.56  fof(f14,plain,(
% 1.36/0.56    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.36/0.56    inference(flattening,[],[f13])).
% 1.36/0.56  fof(f13,plain,(
% 1.36/0.56    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.36/0.56    inference(ennf_transformation,[],[f6])).
% 1.36/0.56  fof(f6,axiom,(
% 1.36/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.36/0.56  fof(f96,plain,(
% 1.36/0.56    ~r1_ordinal1(k1_ordinal1(sK0),sK1)),
% 1.36/0.56    inference(resolution,[],[f95,f21])).
% 1.36/0.56  fof(f21,plain,(
% 1.36/0.56    ~r2_hidden(sK0,sK1) | ~r1_ordinal1(k1_ordinal1(sK0),sK1)),
% 1.36/0.56    inference(cnf_transformation,[],[f11])).
% 1.36/0.56  fof(f167,plain,(
% 1.36/0.56    ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 1.36/0.56    inference(subsumption_resolution,[],[f139,f51])).
% 1.36/0.56  fof(f51,plain,(
% 1.36/0.56    ( ! [X2] : (~r2_hidden(X2,X2)) )),
% 1.36/0.56    inference(resolution,[],[f49,f36])).
% 1.36/0.56  fof(f36,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f19])).
% 1.36/0.56  fof(f19,plain,(
% 1.36/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.36/0.56    inference(ennf_transformation,[],[f8])).
% 1.36/0.56  fof(f8,axiom,(
% 1.36/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.36/0.56  fof(f49,plain,(
% 1.36/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.36/0.56    inference(duplicate_literal_removal,[],[f48])).
% 1.36/0.56  fof(f48,plain,(
% 1.36/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.36/0.56    inference(resolution,[],[f32,f31])).
% 1.36/0.56  fof(f31,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f18])).
% 1.36/0.56  fof(f32,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f18])).
% 1.36/0.56  fof(f139,plain,(
% 1.36/0.56    r2_hidden(sK0,sK0) | ~r2_hidden(sK1,k1_ordinal1(sK0))),
% 1.36/0.56    inference(backward_demodulation,[],[f91,f129])).
% 1.36/0.56  fof(f91,plain,(
% 1.36/0.56    ~r2_hidden(sK1,k1_ordinal1(sK0)) | r2_hidden(sK0,sK1)),
% 1.36/0.56    inference(resolution,[],[f89,f36])).
% 1.36/0.56  % SZS output end Proof for theBenchmark
% 1.36/0.56  % (10388)------------------------------
% 1.36/0.56  % (10388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (10388)Termination reason: Refutation
% 1.36/0.56  
% 1.36/0.56  % (10388)Memory used [KB]: 6268
% 1.36/0.56  % (10388)Time elapsed: 0.123 s
% 1.36/0.56  % (10388)------------------------------
% 1.36/0.56  % (10388)------------------------------
% 1.36/0.56  % (10381)Success in time 0.195 s
%------------------------------------------------------------------------------
