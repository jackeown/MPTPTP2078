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
% DateTime   : Thu Dec  3 12:55:32 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 261 expanded)
%              Number of leaves         :    8 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  146 ( 727 expanded)
%              Number of equality atoms :   20 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(subsumption_resolution,[],[f252,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

% (10759)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f252,plain,(
    r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f251,f208])).

fof(f208,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f207,f140])).

fof(f140,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f138,f95])).

fof(f95,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f94,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f30])).

fof(f30,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f94,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f88,f34])).

fof(f88,plain,
    ( r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(subsumption_resolution,[],[f86,f28])).

fof(f28,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f86,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f56,f75])).

fof(f75,plain,(
    ! [X3] :
      ( r1_ordinal1(sK0,X3)
      | ~ v3_ordinal1(X3)
      | r2_hidden(X3,sK0) ) ),
    inference(resolution,[],[f29,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f29,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f27,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f138,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f70,f29])).

fof(f70,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | r2_hidden(sK1,X2)
      | sK1 = X2
      | r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f28,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f207,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f204,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f204,plain,
    ( r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f203,f28])).

fof(f203,plain,
    ( sK0 = sK1
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f192,f73])).

fof(f73,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(sK0,X1)
      | r1_tarski(sK0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f29,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

% (10749)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f192,plain,
    ( r1_ordinal1(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f98,f57])).

fof(f57,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | r1_ordinal1(sK0,sK1) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f26,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f98,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | sK0 = sK1 ),
    inference(resolution,[],[f95,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f44,f30])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f251,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f217,f64])).

fof(f64,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f46,f30])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f217,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))
    | r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f88,f208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:49:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.22/0.51  % (10746)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.22/0.52  % (10754)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.22/0.52  % (10738)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.53  % (10735)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.53  % (10737)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.54  % (10734)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.54  % (10736)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.54  % (10754)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.33/0.54  % (10753)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.54  % SZS output start Proof for theBenchmark
% 1.33/0.54  fof(f253,plain,(
% 1.33/0.54    $false),
% 1.33/0.54    inference(subsumption_resolution,[],[f252,f34])).
% 1.33/0.54  fof(f34,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f21])).
% 1.33/0.54  % (10759)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.33/0.54    inference(ennf_transformation,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.33/0.54  fof(f252,plain,(
% 1.33/0.54    r2_hidden(sK0,sK0)),
% 1.33/0.54    inference(forward_demodulation,[],[f251,f208])).
% 1.33/0.54  fof(f208,plain,(
% 1.33/0.54    sK0 = sK1),
% 1.33/0.54    inference(subsumption_resolution,[],[f207,f140])).
% 1.33/0.54  fof(f140,plain,(
% 1.33/0.54    r2_hidden(sK1,sK0) | sK0 = sK1),
% 1.33/0.54    inference(subsumption_resolution,[],[f138,f95])).
% 1.33/0.54  fof(f95,plain,(
% 1.33/0.54    ~r2_hidden(sK0,sK1)),
% 1.33/0.54    inference(subsumption_resolution,[],[f94,f59])).
% 1.33/0.54  fof(f59,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 1.33/0.54    inference(definition_unfolding,[],[f45,f30])).
% 1.33/0.54  fof(f30,plain,(
% 1.33/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f7])).
% 1.33/0.54  fof(f7,axiom,(
% 1.33/0.54    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.33/0.54  fof(f45,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f9])).
% 1.33/0.54  fof(f9,axiom,(
% 1.33/0.54    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.33/0.54  fof(f94,plain,(
% 1.33/0.54    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~r2_hidden(sK0,sK1)),
% 1.33/0.54    inference(resolution,[],[f88,f34])).
% 1.33/0.54  fof(f88,plain,(
% 1.33/0.54    r2_hidden(sK1,sK0) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.33/0.54    inference(subsumption_resolution,[],[f86,f28])).
% 1.33/0.54  fof(f28,plain,(
% 1.33/0.54    v3_ordinal1(sK1)),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f15,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f14])).
% 1.33/0.54  fof(f14,negated_conjecture,(
% 1.33/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.33/0.54    inference(negated_conjecture,[],[f13])).
% 1.33/0.54  fof(f13,conjecture,(
% 1.33/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.33/0.54  fof(f86,plain,(
% 1.33/0.54    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~v3_ordinal1(sK1) | r2_hidden(sK1,sK0)),
% 1.33/0.54    inference(resolution,[],[f56,f75])).
% 1.33/0.54  fof(f75,plain,(
% 1.33/0.54    ( ! [X3] : (r1_ordinal1(sK0,X3) | ~v3_ordinal1(X3) | r2_hidden(X3,sK0)) )),
% 1.33/0.54    inference(resolution,[],[f29,f31])).
% 1.33/0.54  fof(f31,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f17])).
% 1.33/0.54  fof(f17,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.33/0.54    inference(flattening,[],[f16])).
% 1.33/0.54  fof(f16,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f11])).
% 1.33/0.54  fof(f11,axiom,(
% 1.33/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.33/0.54  fof(f29,plain,(
% 1.33/0.54    v3_ordinal1(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f56,plain,(
% 1.33/0.54    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.33/0.54    inference(definition_unfolding,[],[f27,f30])).
% 1.33/0.54  fof(f27,plain,(
% 1.33/0.54    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f138,plain,(
% 1.33/0.54    r2_hidden(sK1,sK0) | sK0 = sK1 | r2_hidden(sK0,sK1)),
% 1.33/0.54    inference(resolution,[],[f70,f29])).
% 1.33/0.54  fof(f70,plain,(
% 1.33/0.54    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(sK1,X2) | sK1 = X2 | r2_hidden(X2,sK1)) )),
% 1.33/0.54    inference(resolution,[],[f28,f32])).
% 1.33/0.54  fof(f32,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f19])).
% 1.33/0.54  fof(f19,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.33/0.54    inference(flattening,[],[f18])).
% 1.33/0.54  fof(f18,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f10])).
% 1.33/0.54  fof(f10,axiom,(
% 1.33/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.33/0.54  fof(f207,plain,(
% 1.33/0.54    sK0 = sK1 | ~r2_hidden(sK1,sK0)),
% 1.33/0.54    inference(resolution,[],[f204,f49])).
% 1.33/0.54  fof(f49,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f25])).
% 1.33/0.54  fof(f25,plain,(
% 1.33/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.33/0.54    inference(ennf_transformation,[],[f12])).
% 1.33/0.54  fof(f12,axiom,(
% 1.33/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.33/0.54  fof(f204,plain,(
% 1.33/0.54    r1_tarski(sK0,sK1) | sK0 = sK1),
% 1.33/0.54    inference(subsumption_resolution,[],[f203,f28])).
% 1.33/0.54  fof(f203,plain,(
% 1.33/0.54    sK0 = sK1 | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1)),
% 1.33/0.54    inference(resolution,[],[f192,f73])).
% 1.33/0.54  fof(f73,plain,(
% 1.33/0.54    ( ! [X1] : (~r1_ordinal1(sK0,X1) | r1_tarski(sK0,X1) | ~v3_ordinal1(X1)) )),
% 1.33/0.54    inference(resolution,[],[f29,f36])).
% 1.33/0.54  fof(f36,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f23])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.33/0.54    inference(flattening,[],[f22])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f8])).
% 1.33/0.54  fof(f8,axiom,(
% 1.33/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.33/0.54  % (10749)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.54  fof(f192,plain,(
% 1.33/0.54    r1_ordinal1(sK0,sK1) | sK0 = sK1),
% 1.33/0.54    inference(resolution,[],[f98,f57])).
% 1.33/0.54  fof(f57,plain,(
% 1.33/0.54    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | r1_ordinal1(sK0,sK1)),
% 1.33/0.54    inference(definition_unfolding,[],[f26,f30])).
% 1.33/0.54  fof(f26,plain,(
% 1.33/0.54    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.33/0.54    inference(cnf_transformation,[],[f15])).
% 1.33/0.54  fof(f98,plain,(
% 1.33/0.54    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | sK0 = sK1),
% 1.33/0.54    inference(resolution,[],[f95,f60])).
% 1.33/0.54  fof(f60,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 1.33/0.54    inference(definition_unfolding,[],[f44,f30])).
% 1.33/0.54  fof(f44,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f9])).
% 1.33/0.54  fof(f251,plain,(
% 1.33/0.54    r2_hidden(sK1,sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f217,f64])).
% 1.33/0.54  fof(f64,plain,(
% 1.33/0.54    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 1.33/0.54    inference(equality_resolution,[],[f58])).
% 1.33/0.54  fof(f58,plain,(
% 1.33/0.54    ( ! [X0,X1] : (X0 != X1 | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 1.33/0.54    inference(definition_unfolding,[],[f46,f30])).
% 1.33/0.54  fof(f46,plain,(
% 1.33/0.54    ( ! [X0,X1] : (X0 != X1 | r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f9])).
% 1.33/0.54  fof(f217,plain,(
% 1.33/0.54    ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) | r2_hidden(sK1,sK0)),
% 1.33/0.54    inference(backward_demodulation,[],[f88,f208])).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (10754)------------------------------
% 1.33/0.54  % (10754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (10754)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (10754)Memory used [KB]: 1791
% 1.33/0.54  % (10754)Time elapsed: 0.124 s
% 1.33/0.54  % (10754)------------------------------
% 1.33/0.54  % (10754)------------------------------
% 1.33/0.54  % (10732)Success in time 0.181 s
%------------------------------------------------------------------------------
