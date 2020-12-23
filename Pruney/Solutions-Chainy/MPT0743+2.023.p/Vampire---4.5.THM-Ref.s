%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 269 expanded)
%              Number of leaves         :    8 (  60 expanded)
%              Depth                    :   19
%              Number of atoms          :  144 ( 786 expanded)
%              Number of equality atoms :    4 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f570,plain,(
    $false ),
    inference(subsumption_resolution,[],[f569,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f569,plain,(
    r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f568,f467])).

fof(f467,plain,(
    sK0 = sK1 ),
    inference(unit_resulting_resolution,[],[f132,f446,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | X0 = X1
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f446,plain,(
    r2_hidden(sK1,k1_ordinal1(sK0)) ),
    inference(unit_resulting_resolution,[],[f26,f43,f386,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f386,plain,(
    ~ r1_ordinal1(k1_ordinal1(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f385,f25])).

fof(f25,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_ordinal1(k1_ordinal1(sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).

% (24395)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f385,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f384,f27])).

fof(f27,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f384,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f383,f45])).

fof(f45,plain,(
    ! [X0] : ~ r1_tarski(k1_ordinal1(X0),X0) ),
    inference(unit_resulting_resolution,[],[f41,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f41,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f383,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k1_ordinal1(sK0),sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(factoring,[],[f136])).

fof(f136,plain,(
    ! [X0] :
      ( r2_hidden(sK0,sK1)
      | r1_tarski(k1_ordinal1(sK0),X0)
      | r2_hidden(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f135,f26])).

fof(f135,plain,(
    ! [X0] :
      ( r2_hidden(sK0,sK1)
      | r1_tarski(k1_ordinal1(sK0),X0)
      | ~ v3_ordinal1(sK1)
      | r2_hidden(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f65,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r2_hidden(sK0,sK1)
      | r1_tarski(k1_ordinal1(sK0),X0) ) ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f58,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f57,f43])).

fof(f57,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f54,f26])).

fof(f54,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f29,f24])).

fof(f24,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(unit_resulting_resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f26,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f132,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f131,f36])).

fof(f131,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f66,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f58,f35])).

fof(f568,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f476,f69])).

fof(f69,plain,(
    ~ r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f27,f43,f45,f29])).

fof(f476,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f24,f467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:29:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (24375)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (24400)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.51  % (24391)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (24391)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (24394)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (24380)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (24376)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (24371)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (24373)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (24386)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (24374)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (24372)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (24377)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (24379)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (24397)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (24402)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (24398)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (24392)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (24399)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f570,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f569,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.55  fof(f569,plain,(
% 0.22/0.55    r2_hidden(sK0,sK0)),
% 0.22/0.55    inference(forward_demodulation,[],[f568,f467])).
% 0.22/0.55  fof(f467,plain,(
% 0.22/0.55    sK0 = sK1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f132,f446,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | X0 = X1 | r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.22/0.55  fof(f446,plain,(
% 0.22/0.55    r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f26,f43,f386,f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.55    inference(flattening,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.55  fof(f386,plain,(
% 0.22/0.55    ~r1_ordinal1(k1_ordinal1(sK0),sK1)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f385,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ~r2_hidden(sK0,sK1) | ~r1_ordinal1(k1_ordinal1(sK0),sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  % (24395)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,negated_conjecture,(
% 0.22/0.55    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.55    inference(negated_conjecture,[],[f12])).
% 0.22/0.55  fof(f12,conjecture,(
% 0.22/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.22/0.55  fof(f385,plain,(
% 0.22/0.55    r2_hidden(sK0,sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f384,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    v3_ordinal1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f384,plain,(
% 0.22/0.55    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f383,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k1_ordinal1(X0),X0)) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f41,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.22/0.55    inference(equality_resolution,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X0,X1] : (X0 != X1 | r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f383,plain,(
% 0.22/0.55    r2_hidden(sK0,sK1) | r1_tarski(k1_ordinal1(sK0),sK0) | ~v3_ordinal1(sK0)),
% 0.22/0.55    inference(factoring,[],[f136])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK0,sK1) | r1_tarski(k1_ordinal1(sK0),X0) | r2_hidden(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f135,f26])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK0,sK1) | r1_tarski(k1_ordinal1(sK0),X0) | ~v3_ordinal1(sK1) | r2_hidden(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.22/0.55    inference(resolution,[],[f65,f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X0) | r1_tarski(X1,X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.55    inference(resolution,[],[f30,f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.55    inference(flattening,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK0,sK1) | r1_tarski(k1_ordinal1(sK0),X0)) )),
% 0.22/0.55    inference(resolution,[],[f58,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    r1_tarski(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f57,f43])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | r2_hidden(sK0,sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f54,f26])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ~v3_ordinal1(sK1) | r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | r2_hidden(sK0,sK1)),
% 0.22/0.55    inference(resolution,[],[f29,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    v3_ordinal1(k1_ordinal1(sK0))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f27,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    v3_ordinal1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    ~r2_hidden(sK1,sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f131,f36])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 0.22/0.55    inference(resolution,[],[f66,f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ~r2_hidden(sK1,k1_ordinal1(sK0)) | r2_hidden(sK0,sK1)),
% 0.22/0.55    inference(resolution,[],[f58,f35])).
% 0.22/0.55  fof(f568,plain,(
% 0.22/0.55    r2_hidden(sK0,sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f476,f69])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ~r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f27,f43,f45,f29])).
% 0.22/0.55  fof(f476,plain,(
% 0.22/0.55    r1_ordinal1(k1_ordinal1(sK0),sK0) | r2_hidden(sK0,sK1)),
% 0.22/0.55    inference(backward_demodulation,[],[f24,f467])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (24391)------------------------------
% 0.22/0.55  % (24391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24391)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (24391)Memory used [KB]: 1918
% 0.22/0.55  % (24391)Time elapsed: 0.124 s
% 0.22/0.55  % (24391)------------------------------
% 0.22/0.55  % (24391)------------------------------
% 0.22/0.55  % (24368)Success in time 0.186 s
%------------------------------------------------------------------------------
