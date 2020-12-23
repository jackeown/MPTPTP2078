%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:13 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   43 (  76 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 154 expanded)
%              Number of equality atoms :   36 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(subsumption_resolution,[],[f98,f67])).

fof(f67,plain,(
    ! [X0] : r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(resolution,[],[f49,f62])).

fof(f62,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f22])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f98,plain,(
    ~ r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    inference(subsumption_resolution,[],[f96,f75])).

fof(f75,plain,(
    r2_hidden(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f40,f45])).

fof(f45,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),sK3))
    | r2_hidden(sK1,sK3) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f96,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK0)) ),
    inference(resolution,[],[f95,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f95,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),sK3)) ),
    inference(subsumption_resolution,[],[f94,f75])).

fof(f94,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),sK3)) ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),sK3)) ),
    inference(backward_demodulation,[],[f66,f90])).

fof(f90,plain,(
    sK0 = sK2 ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( sK0 = sK2
    | sK0 = sK2 ),
    inference(resolution,[],[f83,f71])).

fof(f71,plain,
    ( r2_hidden(sK0,k2_tarski(sK2,sK2))
    | sK0 = sK2 ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),sK3))
    | sK0 = sK2 ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f20,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k2_tarski(X3,X3))
      | X3 = X4 ) ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,(
    ! [X4,X3] :
      ( k2_tarski(X3,X3) != k2_tarski(X3,X3)
      | ~ r2_hidden(X4,k2_tarski(X3,X3))
      | X3 = X4 ) ),
    inference(superposition,[],[f51,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f29,f22,f22,f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f28,f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f66,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),sK3)) ),
    inference(inner_rewriting,[],[f47])).

fof(f47,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f19,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (25969)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (25963)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (25967)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (25972)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.18/0.51  % (25968)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.18/0.52  % (25986)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.18/0.52  % (25973)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.18/0.52  % (25969)Refutation found. Thanks to Tanya!
% 1.18/0.52  % SZS status Theorem for theBenchmark
% 1.18/0.52  % SZS output start Proof for theBenchmark
% 1.18/0.52  fof(f99,plain,(
% 1.18/0.52    $false),
% 1.18/0.52    inference(subsumption_resolution,[],[f98,f67])).
% 1.18/0.52  fof(f67,plain,(
% 1.18/0.52    ( ! [X0] : (r2_hidden(X0,k2_tarski(X0,X0))) )),
% 1.18/0.52    inference(resolution,[],[f49,f62])).
% 1.18/0.52  fof(f62,plain,(
% 1.18/0.52    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 1.18/0.52    inference(equality_resolution,[],[f37])).
% 1.18/0.52  fof(f37,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.18/0.52    inference(cnf_transformation,[],[f16])).
% 1.18/0.52  fof(f16,plain,(
% 1.18/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.18/0.52    inference(ennf_transformation,[],[f3])).
% 1.18/0.52  fof(f3,axiom,(
% 1.18/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.18/0.52  fof(f49,plain,(
% 1.18/0.52    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.18/0.52    inference(definition_unfolding,[],[f26,f22])).
% 1.18/0.52  fof(f22,plain,(
% 1.18/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f2])).
% 1.18/0.52  fof(f2,axiom,(
% 1.18/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.18/0.52  fof(f26,plain,(
% 1.18/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f9])).
% 1.18/0.52  fof(f9,axiom,(
% 1.18/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 1.18/0.52  fof(f98,plain,(
% 1.18/0.52    ~r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 1.18/0.52    inference(subsumption_resolution,[],[f96,f75])).
% 1.18/0.52  fof(f75,plain,(
% 1.18/0.52    r2_hidden(sK1,sK3)),
% 1.18/0.52    inference(duplicate_literal_removal,[],[f74])).
% 1.18/0.52  fof(f74,plain,(
% 1.18/0.52    r2_hidden(sK1,sK3) | r2_hidden(sK1,sK3)),
% 1.18/0.52    inference(resolution,[],[f40,f45])).
% 1.18/0.52  fof(f45,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),sK3)) | r2_hidden(sK1,sK3)),
% 1.18/0.52    inference(definition_unfolding,[],[f21,f22])).
% 1.18/0.52  fof(f21,plain,(
% 1.18/0.52    r2_hidden(sK1,sK3) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.18/0.52    inference(cnf_transformation,[],[f14])).
% 1.18/0.52  fof(f14,plain,(
% 1.18/0.52    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <~> (r2_hidden(X1,X3) & X0 = X2))),
% 1.18/0.52    inference(ennf_transformation,[],[f13])).
% 1.18/0.52  fof(f13,negated_conjecture,(
% 1.18/0.52    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.18/0.52    inference(negated_conjecture,[],[f12])).
% 1.18/0.52  fof(f12,conjecture,(
% 1.18/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 1.18/0.52  fof(f40,plain,(
% 1.18/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f5])).
% 1.18/0.52  fof(f5,axiom,(
% 1.18/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 1.18/0.52  fof(f96,plain,(
% 1.18/0.52    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK0,k2_tarski(sK0,sK0))),
% 1.18/0.52    inference(resolution,[],[f95,f41])).
% 1.18/0.52  fof(f41,plain,(
% 1.18/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f5])).
% 1.18/0.52  fof(f95,plain,(
% 1.18/0.52    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),sK3))),
% 1.18/0.52    inference(subsumption_resolution,[],[f94,f75])).
% 1.18/0.52  fof(f94,plain,(
% 1.18/0.52    ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),sK3))),
% 1.18/0.52    inference(trivial_inequality_removal,[],[f92])).
% 1.18/0.52  fof(f92,plain,(
% 1.18/0.52    sK0 != sK0 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),sK3))),
% 1.18/0.52    inference(backward_demodulation,[],[f66,f90])).
% 1.18/0.52  fof(f90,plain,(
% 1.18/0.52    sK0 = sK2),
% 1.18/0.52    inference(duplicate_literal_removal,[],[f88])).
% 1.18/0.52  fof(f88,plain,(
% 1.18/0.52    sK0 = sK2 | sK0 = sK2),
% 1.18/0.52    inference(resolution,[],[f83,f71])).
% 1.18/0.52  fof(f71,plain,(
% 1.18/0.52    r2_hidden(sK0,k2_tarski(sK2,sK2)) | sK0 = sK2),
% 1.18/0.52    inference(resolution,[],[f39,f46])).
% 1.18/0.52  fof(f46,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),sK3)) | sK0 = sK2),
% 1.18/0.52    inference(definition_unfolding,[],[f20,f22])).
% 1.18/0.52  fof(f20,plain,(
% 1.18/0.52    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.18/0.52    inference(cnf_transformation,[],[f14])).
% 1.18/0.52  fof(f39,plain,(
% 1.18/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f5])).
% 1.18/0.52  fof(f83,plain,(
% 1.18/0.52    ( ! [X4,X3] : (~r2_hidden(X4,k2_tarski(X3,X3)) | X3 = X4) )),
% 1.18/0.52    inference(trivial_inequality_removal,[],[f82])).
% 1.18/0.52  fof(f82,plain,(
% 1.18/0.52    ( ! [X4,X3] : (k2_tarski(X3,X3) != k2_tarski(X3,X3) | ~r2_hidden(X4,k2_tarski(X3,X3)) | X3 = X4) )),
% 1.18/0.52    inference(superposition,[],[f51,f54])).
% 1.18/0.52  fof(f54,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) | X0 = X1) )),
% 1.18/0.52    inference(definition_unfolding,[],[f29,f22,f22,f22])).
% 1.18/0.52  fof(f29,plain,(
% 1.18/0.52    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.18/0.52    inference(cnf_transformation,[],[f7])).
% 1.18/0.52  fof(f7,axiom,(
% 1.18/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.18/0.52  fof(f51,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.18/0.52    inference(definition_unfolding,[],[f28,f22])).
% 1.18/0.52  fof(f28,plain,(
% 1.18/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.18/0.52    inference(cnf_transformation,[],[f11])).
% 1.18/0.52  fof(f11,axiom,(
% 1.18/0.52    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.18/0.52  fof(f66,plain,(
% 1.18/0.52    sK0 != sK2 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK0,sK0),sK3))),
% 1.18/0.52    inference(inner_rewriting,[],[f47])).
% 1.18/0.52  fof(f47,plain,(
% 1.18/0.52    sK0 != sK2 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_tarski(sK2,sK2),sK3))),
% 1.18/0.52    inference(definition_unfolding,[],[f19,f22])).
% 1.18/0.52  fof(f19,plain,(
% 1.18/0.52    sK0 != sK2 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.18/0.52    inference(cnf_transformation,[],[f14])).
% 1.18/0.52  % SZS output end Proof for theBenchmark
% 1.18/0.52  % (25969)------------------------------
% 1.18/0.52  % (25969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (25969)Termination reason: Refutation
% 1.18/0.52  
% 1.18/0.52  % (25969)Memory used [KB]: 6268
% 1.18/0.52  % (25969)Time elapsed: 0.103 s
% 1.18/0.52  % (25969)------------------------------
% 1.18/0.52  % (25969)------------------------------
% 1.18/0.52  % (25980)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.18/0.52  % (25960)Success in time 0.159 s
%------------------------------------------------------------------------------
