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
% DateTime   : Thu Dec  3 12:55:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 827 expanded)
%              Number of leaves         :    8 ( 170 expanded)
%              Depth                    :   21
%              Number of atoms          :  170 (2833 expanded)
%              Number of equality atoms :   31 ( 537 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f558,plain,(
    $false ),
    inference(subsumption_resolution,[],[f526,f459])).

fof(f459,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f60,f440])).

fof(f440,plain,(
    sK0 = sK3(sK1,sK0) ),
    inference(subsumption_resolution,[],[f416,f370])).

fof(f370,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = sK3(sK1,sK0) ),
    inference(resolution,[],[f355,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f355,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK3(sK1,sK0) ),
    inference(resolution,[],[f346,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,sK2(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(f346,plain,
    ( r2_hidden(sK0,sK2(sK1))
    | sK0 = sK3(sK1,sK0) ),
    inference(resolution,[],[f345,f93])).

fof(f93,plain,
    ( ~ r2_hidden(sK0,sK3(sK1,sK0))
    | r2_hidden(sK0,sK2(sK1)) ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(X0,sK3(sK1,sK0)) ) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_ordinal1)).

fof(f54,plain,(
    r2_hidden(sK3(sK1,sK0),sK1) ),
    inference(resolution,[],[f52,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f52,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f51,f23])).

fof(f23,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ~ ( ~ r2_xboole_0(X1,X0)
                & X0 != X1
                & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

fof(f51,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f24,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f24,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f86,plain,
    ( r2_hidden(sK1,sK0)
    | r2_hidden(sK0,sK2(sK1)) ),
    inference(resolution,[],[f85,f48])).

fof(f48,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,X1)
      | r2_hidden(sK0,sK2(X1)) ) ),
    inference(resolution,[],[f25,f29])).

fof(f29,plain,(
    ! [X2,X0] :
      ( ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,sK2(X0)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f85,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f81,f23])).

fof(f81,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f46,f25])).

fof(f46,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | r2_hidden(sK1,X2)
      | sK1 = X2
      | r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f21,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f21,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f345,plain,
    ( r2_hidden(sK0,sK3(sK1,sK0))
    | sK0 = sK3(sK1,sK0) ),
    inference(subsumption_resolution,[],[f337,f52])).

fof(f337,plain,
    ( sK0 = sK3(sK1,sK0)
    | r2_hidden(sK0,sK3(sK1,sK0))
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f127,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f127,plain,
    ( r2_hidden(sK3(sK1,sK0),sK0)
    | sK0 = sK3(sK1,sK0)
    | r2_hidden(sK0,sK3(sK1,sK0)) ),
    inference(resolution,[],[f49,f55])).

fof(f55,plain,(
    v3_ordinal1(sK3(sK1,sK0)) ),
    inference(resolution,[],[f54,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | v3_ordinal1(X0) ) ),
    inference(resolution,[],[f21,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f49,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | r2_hidden(sK0,X2)
      | sK0 = X2
      | r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f25,f26])).

fof(f416,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK3(sK1,sK0) ),
    inference(superposition,[],[f66,f362])).

fof(f362,plain,
    ( sK1 = sK3(sK0,sK1)
    | sK0 = sK3(sK1,sK0) ),
    inference(resolution,[],[f355,f295])).

fof(f295,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = sK3(sK0,sK1) ),
    inference(resolution,[],[f290,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(sK0,sK1))
      | ~ r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f66,f42])).

fof(f290,plain,
    ( r2_hidden(sK1,sK3(sK0,sK1))
    | sK1 = sK3(sK0,sK1) ),
    inference(subsumption_resolution,[],[f281,f64])).

fof(f64,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f50,f23])).

fof(f50,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f22,f37])).

fof(f22,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f281,plain,
    ( sK1 = sK3(sK0,sK1)
    | r2_hidden(sK1,sK3(sK0,sK1))
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f83,f34])).

fof(f83,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | sK1 = sK3(sK0,sK1)
    | r2_hidden(sK1,sK3(sK0,sK1)) ),
    inference(resolution,[],[f46,f67])).

fof(f67,plain,(
    v3_ordinal1(sK3(sK0,sK1)) ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v3_ordinal1(X0) ) ),
    inference(resolution,[],[f25,f30])).

fof(f66,plain,(
    r2_hidden(sK3(sK0,sK1),sK0) ),
    inference(resolution,[],[f64,f33])).

fof(f60,plain,(
    ~ r2_hidden(sK1,sK3(sK1,sK0)) ),
    inference(resolution,[],[f54,f31])).

fof(f526,plain,(
    r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f66,f524])).

fof(f524,plain,(
    sK1 = sK3(sK0,sK1) ),
    inference(resolution,[],[f511,f290])).

fof(f511,plain,(
    ~ r2_hidden(sK1,sK3(sK0,sK1)) ),
    inference(resolution,[],[f456,f66])).

fof(f456,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK1,X0) ) ),
    inference(backward_demodulation,[],[f56,f440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (4361)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (4345)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (4353)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (4346)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (4340)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (4343)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (4363)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (4341)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (4355)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (4362)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (4347)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (4362)Refutation not found, incomplete strategy% (4362)------------------------------
% 0.20/0.53  % (4362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4362)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4362)Memory used [KB]: 10618
% 0.20/0.53  % (4362)Time elapsed: 0.127 s
% 0.20/0.53  % (4362)------------------------------
% 0.20/0.53  % (4362)------------------------------
% 0.20/0.53  % (4361)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (4344)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (4366)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f558,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f526,f459])).
% 0.20/0.53  fof(f459,plain,(
% 0.20/0.53    ~r2_hidden(sK1,sK0)),
% 0.20/0.53    inference(backward_demodulation,[],[f60,f440])).
% 0.20/0.53  fof(f440,plain,(
% 0.20/0.53    sK0 = sK3(sK1,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f416,f370])).
% 0.20/0.53  fof(f370,plain,(
% 0.20/0.53    ~r2_hidden(sK1,sK0) | sK0 = sK3(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f355,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.53  fof(f355,plain,(
% 0.20/0.53    r2_hidden(sK0,sK1) | sK0 = sK3(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f346,f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~r2_hidden(X2,sK2(X0)) | r2_hidden(X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : ? [X1] : ! [X2] : (r2_hidden(X2,X1) <=> (v3_ordinal1(X2) & r2_hidden(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).
% 0.20/0.53  fof(f346,plain,(
% 0.20/0.53    r2_hidden(sK0,sK2(sK1)) | sK0 = sK3(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f345,f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    ~r2_hidden(sK0,sK3(sK1,sK0)) | r2_hidden(sK0,sK2(sK1))),
% 0.20/0.53    inference(resolution,[],[f86,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK1,X0) | ~r2_hidden(X0,sK3(sK1,sK0))) )),
% 0.20/0.53    inference(resolution,[],[f54,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ~(r2_hidden(X2,X0) & r2_hidden(X1,X2) & r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_ordinal1)).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    r2_hidden(sK3(sK1,sK0),sK1)),
% 0.20/0.53    inference(resolution,[],[f52,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ~r1_tarski(sK1,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f51,f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    sK0 != sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.53    inference(flattening,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f10])).
% 0.20/0.53  fof(f10,conjecture,(
% 0.20/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    sK0 = sK1 | ~r1_tarski(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f24,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ~r2_xboole_0(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    r2_hidden(sK1,sK0) | r2_hidden(sK0,sK2(sK1))),
% 0.20/0.53    inference(resolution,[],[f85,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X1] : (~r2_hidden(sK0,X1) | r2_hidden(sK0,sK2(X1))) )),
% 0.20/0.53    inference(resolution,[],[f25,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~v3_ordinal1(X2) | ~r2_hidden(X2,X0) | r2_hidden(X2,sK2(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    v3_ordinal1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    r2_hidden(sK0,sK1) | r2_hidden(sK1,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f81,f23])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    r2_hidden(sK1,sK0) | sK0 = sK1 | r2_hidden(sK0,sK1)),
% 0.20/0.53    inference(resolution,[],[f46,f25])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(sK1,X2) | sK1 = X2 | r2_hidden(X2,sK1)) )),
% 0.20/0.53    inference(resolution,[],[f21,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(flattening,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    v3_ordinal1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f345,plain,(
% 0.20/0.53    r2_hidden(sK0,sK3(sK1,sK0)) | sK0 = sK3(sK1,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f337,f52])).
% 0.20/0.53  fof(f337,plain,(
% 0.20/0.53    sK0 = sK3(sK1,sK0) | r2_hidden(sK0,sK3(sK1,sK0)) | r1_tarski(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f127,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    r2_hidden(sK3(sK1,sK0),sK0) | sK0 = sK3(sK1,sK0) | r2_hidden(sK0,sK3(sK1,sK0))),
% 0.20/0.53    inference(resolution,[],[f49,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    v3_ordinal1(sK3(sK1,sK0))),
% 0.20/0.53    inference(resolution,[],[f54,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | v3_ordinal1(X0)) )),
% 0.20/0.53    inference(resolution,[],[f21,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | v3_ordinal1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X2] : (~v3_ordinal1(X2) | r2_hidden(sK0,X2) | sK0 = X2 | r2_hidden(X2,sK0)) )),
% 0.20/0.53    inference(resolution,[],[f25,f26])).
% 0.20/0.53  fof(f416,plain,(
% 0.20/0.53    r2_hidden(sK1,sK0) | sK0 = sK3(sK1,sK0)),
% 0.20/0.53    inference(superposition,[],[f66,f362])).
% 0.20/0.53  fof(f362,plain,(
% 0.20/0.53    sK1 = sK3(sK0,sK1) | sK0 = sK3(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f355,f295])).
% 0.20/0.53  fof(f295,plain,(
% 0.20/0.53    ~r2_hidden(sK0,sK1) | sK1 = sK3(sK0,sK1)),
% 0.20/0.53    inference(resolution,[],[f290,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK3(sK0,sK1)) | ~r2_hidden(sK0,X0)) )),
% 0.20/0.53    inference(resolution,[],[f66,f42])).
% 0.20/0.53  fof(f290,plain,(
% 0.20/0.53    r2_hidden(sK1,sK3(sK0,sK1)) | sK1 = sK3(sK0,sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f281,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ~r1_tarski(sK0,sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f50,f23])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    sK0 = sK1 | ~r1_tarski(sK0,sK1)),
% 0.20/0.53    inference(resolution,[],[f22,f37])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ~r2_xboole_0(sK0,sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f281,plain,(
% 0.20/0.54    sK1 = sK3(sK0,sK1) | r2_hidden(sK1,sK3(sK0,sK1)) | r1_tarski(sK0,sK1)),
% 0.20/0.54    inference(resolution,[],[f83,f34])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    r2_hidden(sK3(sK0,sK1),sK1) | sK1 = sK3(sK0,sK1) | r2_hidden(sK1,sK3(sK0,sK1))),
% 0.20/0.54    inference(resolution,[],[f46,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    v3_ordinal1(sK3(sK0,sK1))),
% 0.20/0.54    inference(resolution,[],[f66,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | v3_ordinal1(X0)) )),
% 0.20/0.54    inference(resolution,[],[f25,f30])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    r2_hidden(sK3(sK0,sK1),sK0)),
% 0.20/0.54    inference(resolution,[],[f64,f33])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ~r2_hidden(sK1,sK3(sK1,sK0))),
% 0.20/0.54    inference(resolution,[],[f54,f31])).
% 0.20/0.54  fof(f526,plain,(
% 0.20/0.54    r2_hidden(sK1,sK0)),
% 0.20/0.54    inference(backward_demodulation,[],[f66,f524])).
% 0.20/0.54  fof(f524,plain,(
% 0.20/0.54    sK1 = sK3(sK0,sK1)),
% 0.20/0.54    inference(resolution,[],[f511,f290])).
% 0.20/0.54  fof(f511,plain,(
% 0.20/0.54    ~r2_hidden(sK1,sK3(sK0,sK1))),
% 0.20/0.54    inference(resolution,[],[f456,f66])).
% 0.20/0.54  fof(f456,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(sK1,X0)) )),
% 0.20/0.54    inference(backward_demodulation,[],[f56,f440])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (4361)------------------------------
% 0.20/0.54  % (4361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (4361)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (4361)Memory used [KB]: 1918
% 0.20/0.54  % (4361)Time elapsed: 0.118 s
% 0.20/0.54  % (4361)------------------------------
% 0.20/0.54  % (4361)------------------------------
% 0.20/0.54  % (4357)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (4339)Success in time 0.182 s
%------------------------------------------------------------------------------
