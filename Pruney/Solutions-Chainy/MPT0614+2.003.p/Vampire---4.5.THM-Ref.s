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
% DateTime   : Thu Dec  3 12:51:42 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   55 (  89 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 ( 287 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(subsumption_resolution,[],[f82,f135])).

fof(f135,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f134])).

fof(f134,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f45,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f43,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f82,plain,(
    r2_hidden(sK3(k4_xboole_0(k2_relat_1(sK2),sK1),k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f81,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f81,plain,(
    r2_xboole_0(k4_xboole_0(k2_relat_1(sK2),sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f79,f54])).

fof(f54,plain,(
    k1_xboole_0 != k4_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f52,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f52,plain,(
    ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f51,f31])).

fof(f31,plain,(
    ~ v5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v5_relat_1(sK2,sK1)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v5_relat_1(X2,X1)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ~ v5_relat_1(X2,sK1)
          & v5_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ v5_relat_1(X2,sK1)
        & v5_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ v5_relat_1(sK2,sK1)
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => v5_relat_1(X2,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

fof(f51,plain,(
    ! [X0] :
      ( v5_relat_1(sK2,X0)
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f79,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_relat_1(sK2),sK1)
    | r2_xboole_0(k4_xboole_0(k2_relat_1(sK2),sK1),k1_xboole_0) ),
    inference(resolution,[],[f69,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f69,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK1),k1_xboole_0) ),
    inference(superposition,[],[f60,f50])).

fof(f50,plain,(
    k1_xboole_0 = k4_xboole_0(k2_relat_1(sK2),sK0) ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:52:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (18783)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (18791)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (18775)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (18782)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (18791)Refutation not found, incomplete strategy% (18791)------------------------------
% 0.21/0.52  % (18791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18791)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18791)Memory used [KB]: 10618
% 0.21/0.52  % (18791)Time elapsed: 0.122 s
% 0.21/0.52  % (18791)------------------------------
% 0.21/0.52  % (18791)------------------------------
% 0.21/0.53  % (18769)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (18769)Refutation not found, incomplete strategy% (18769)------------------------------
% 0.21/0.53  % (18769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18769)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18769)Memory used [KB]: 1663
% 0.21/0.53  % (18769)Time elapsed: 0.125 s
% 0.21/0.53  % (18769)------------------------------
% 0.21/0.53  % (18769)------------------------------
% 0.21/0.53  % (18796)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (18795)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (18790)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (18772)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (18771)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (18774)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.41/0.54  % (18793)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.54  % (18797)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.54  % (18774)Refutation found. Thanks to Tanya!
% 1.41/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.54  % SZS output start Proof for theBenchmark
% 1.41/0.54  fof(f136,plain,(
% 1.41/0.54    $false),
% 1.41/0.54    inference(subsumption_resolution,[],[f82,f135])).
% 1.41/0.54  fof(f135,plain,(
% 1.41/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.41/0.54    inference(trivial_inequality_removal,[],[f134])).
% 1.41/0.54  fof(f134,plain,(
% 1.41/0.54    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.41/0.54    inference(superposition,[],[f45,f40])).
% 1.41/0.54  fof(f40,plain,(
% 1.41/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f6])).
% 1.41/0.54  fof(f6,axiom,(
% 1.41/0.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.41/0.54  fof(f45,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.41/0.54    inference(definition_unfolding,[],[f38,f43])).
% 1.41/0.54  fof(f43,plain,(
% 1.41/0.54    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f7])).
% 1.41/0.54  fof(f7,axiom,(
% 1.41/0.54    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
% 1.41/0.54  fof(f38,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.41/0.54    inference(cnf_transformation,[],[f25])).
% 1.41/0.54  fof(f25,plain,(
% 1.41/0.54    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.41/0.54    inference(nnf_transformation,[],[f8])).
% 1.41/0.54  fof(f8,axiom,(
% 1.41/0.54    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.41/0.54  fof(f82,plain,(
% 1.41/0.54    r2_hidden(sK3(k4_xboole_0(k2_relat_1(sK2),sK1),k1_xboole_0),k1_xboole_0)),
% 1.41/0.54    inference(resolution,[],[f81,f41])).
% 1.41/0.54  fof(f41,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f27])).
% 1.41/0.54  fof(f27,plain,(
% 1.41/0.54    ! [X0,X1] : ((~r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f26])).
% 1.41/0.54  fof(f26,plain,(
% 1.41/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1)))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f19,plain,(
% 1.41/0.54    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.41/0.54    inference(ennf_transformation,[],[f3])).
% 1.41/0.54  fof(f3,axiom,(
% 1.41/0.54    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.41/0.54  fof(f81,plain,(
% 1.41/0.54    r2_xboole_0(k4_xboole_0(k2_relat_1(sK2),sK1),k1_xboole_0)),
% 1.41/0.54    inference(subsumption_resolution,[],[f79,f54])).
% 1.41/0.54  fof(f54,plain,(
% 1.41/0.54    k1_xboole_0 != k4_xboole_0(k2_relat_1(sK2),sK1)),
% 1.41/0.54    inference(resolution,[],[f52,f35])).
% 1.41/0.54  fof(f35,plain,(
% 1.41/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.41/0.54    inference(cnf_transformation,[],[f24])).
% 1.41/0.54  fof(f24,plain,(
% 1.41/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.41/0.54    inference(nnf_transformation,[],[f4])).
% 1.41/0.54  fof(f4,axiom,(
% 1.41/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.41/0.54  fof(f52,plain,(
% 1.41/0.54    ~r1_tarski(k2_relat_1(sK2),sK1)),
% 1.41/0.54    inference(resolution,[],[f51,f31])).
% 1.41/0.54  fof(f31,plain,(
% 1.41/0.54    ~v5_relat_1(sK2,sK1)),
% 1.41/0.54    inference(cnf_transformation,[],[f22])).
% 1.41/0.54  fof(f22,plain,(
% 1.41/0.54    (~v5_relat_1(sK2,sK1) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2)) & r1_tarski(sK0,sK1)),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21,f20])).
% 1.41/0.54  fof(f20,plain,(
% 1.41/0.54    ? [X0,X1] : (? [X2] : (~v5_relat_1(X2,X1) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1)) => (? [X2] : (~v5_relat_1(X2,sK1) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & r1_tarski(sK0,sK1))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f21,plain,(
% 1.41/0.54    ? [X2] : (~v5_relat_1(X2,sK1) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) => (~v5_relat_1(sK2,sK1) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f14,plain,(
% 1.41/0.54    ? [X0,X1] : (? [X2] : (~v5_relat_1(X2,X1) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1))),
% 1.41/0.54    inference(flattening,[],[f13])).
% 1.41/0.54  fof(f13,plain,(
% 1.41/0.54    ? [X0,X1] : (? [X2] : (~v5_relat_1(X2,X1) & (v5_relat_1(X2,X0) & v1_relat_1(X2))) & r1_tarski(X0,X1))),
% 1.41/0.54    inference(ennf_transformation,[],[f11])).
% 1.41/0.54  fof(f11,negated_conjecture,(
% 1.41/0.54    ~! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 1.41/0.54    inference(negated_conjecture,[],[f10])).
% 1.41/0.54  fof(f10,conjecture,(
% 1.41/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).
% 1.41/0.54  fof(f51,plain,(
% 1.41/0.54    ( ! [X0] : (v5_relat_1(sK2,X0) | ~r1_tarski(k2_relat_1(sK2),X0)) )),
% 1.41/0.54    inference(resolution,[],[f33,f29])).
% 1.41/0.54  fof(f29,plain,(
% 1.41/0.54    v1_relat_1(sK2)),
% 1.41/0.54    inference(cnf_transformation,[],[f22])).
% 1.41/0.54  fof(f33,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f23])).
% 1.41/0.54  fof(f23,plain,(
% 1.41/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(nnf_transformation,[],[f15])).
% 1.41/0.54  fof(f15,plain,(
% 1.41/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(ennf_transformation,[],[f9])).
% 1.41/0.54  fof(f9,axiom,(
% 1.41/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.41/0.54  fof(f79,plain,(
% 1.41/0.54    k1_xboole_0 = k4_xboole_0(k2_relat_1(sK2),sK1) | r2_xboole_0(k4_xboole_0(k2_relat_1(sK2),sK1),k1_xboole_0)),
% 1.41/0.54    inference(resolution,[],[f69,f37])).
% 1.41/0.54  fof(f37,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f18])).
% 1.41/0.54  fof(f18,plain,(
% 1.41/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.41/0.54    inference(flattening,[],[f17])).
% 1.41/0.54  fof(f17,plain,(
% 1.41/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 1.41/0.54    inference(ennf_transformation,[],[f12])).
% 1.41/0.54  fof(f12,plain,(
% 1.41/0.54    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 1.41/0.54    inference(unused_predicate_definition_removal,[],[f2])).
% 1.41/0.54  fof(f2,axiom,(
% 1.41/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.41/0.54  fof(f69,plain,(
% 1.41/0.54    r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK1),k1_xboole_0)),
% 1.41/0.54    inference(superposition,[],[f60,f50])).
% 1.41/0.54  fof(f50,plain,(
% 1.41/0.54    k1_xboole_0 = k4_xboole_0(k2_relat_1(sK2),sK0)),
% 1.41/0.54    inference(resolution,[],[f49,f36])).
% 1.41/0.54  fof(f36,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.41/0.54    inference(cnf_transformation,[],[f24])).
% 1.41/0.54  fof(f49,plain,(
% 1.41/0.54    r1_tarski(k2_relat_1(sK2),sK0)),
% 1.41/0.54    inference(resolution,[],[f48,f30])).
% 1.41/0.54  fof(f30,plain,(
% 1.41/0.54    v5_relat_1(sK2,sK0)),
% 1.41/0.54    inference(cnf_transformation,[],[f22])).
% 1.41/0.54  fof(f48,plain,(
% 1.41/0.54    ( ! [X0] : (~v5_relat_1(sK2,X0) | r1_tarski(k2_relat_1(sK2),X0)) )),
% 1.41/0.54    inference(resolution,[],[f32,f29])).
% 1.41/0.54  fof(f32,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f23])).
% 1.41/0.54  fof(f60,plain,(
% 1.41/0.54    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0))) )),
% 1.41/0.54    inference(resolution,[],[f34,f28])).
% 1.41/0.54  fof(f28,plain,(
% 1.41/0.54    r1_tarski(sK0,sK1)),
% 1.41/0.54    inference(cnf_transformation,[],[f22])).
% 1.41/0.54  fof(f34,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f16])).
% 1.41/0.54  fof(f16,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.41/0.54    inference(ennf_transformation,[],[f5])).
% 1.41/0.54  fof(f5,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.41/0.54  % SZS output end Proof for theBenchmark
% 1.41/0.54  % (18774)------------------------------
% 1.41/0.54  % (18774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (18774)Termination reason: Refutation
% 1.41/0.54  
% 1.41/0.54  % (18774)Memory used [KB]: 6268
% 1.41/0.54  % (18774)Time elapsed: 0.140 s
% 1.41/0.54  % (18774)------------------------------
% 1.41/0.54  % (18774)------------------------------
% 1.41/0.54  % (18773)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.54  % (18768)Success in time 0.179 s
%------------------------------------------------------------------------------
