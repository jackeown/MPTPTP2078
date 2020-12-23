%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 109 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  134 ( 233 expanded)
%              Number of equality atoms :   53 ( 130 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(subsumption_resolution,[],[f104,f86])).

fof(f86,plain,(
    k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f41,f85])).

fof(f85,plain,(
    ! [X3] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f84,f70])).

% (30540)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f69,f66])).

fof(f66,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f50,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f52,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f84,plain,(
    ! [X3] : k2_relat_1(k7_relat_1(k1_xboole_0,X3)) = k9_relat_1(k1_xboole_0,X3) ),
    inference(resolution,[],[f53,f66])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f41,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f32])).

fof(f32,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f104,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f100,f75])).

fof(f75,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f100,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f82,f97])).

fof(f97,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f95,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

% (30540)Refutation not found, incomplete strategy% (30540)------------------------------
% (30540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f95,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f94,f72])).

fof(f72,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f60,f43])).

fof(f43,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).

fof(f94,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_relat_1(k1_xboole_0)),X0)
      | v1_xboole_0(k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f93,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f93,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(k1_xboole_0))
      | r2_hidden(X4,X5) ) ),
    inference(forward_demodulation,[],[f92,f70])).

fof(f92,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(k7_relat_1(k1_xboole_0,X5)))
      | r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f61,f66])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

% (30540)Termination reason: Refutation not found, incomplete strategy

% (30540)Memory used [KB]: 1663
% (30540)Time elapsed: 0.103 s
% (30540)------------------------------
% (30540)------------------------------
fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f82,plain,(
    k1_xboole_0 = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f81,f42])).

fof(f42,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

fof(f81,plain,(
    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f47,f66])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (30542)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (30519)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (30526)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (30519)Refutation not found, incomplete strategy% (30519)------------------------------
% 0.21/0.51  % (30519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30526)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (30532)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (30519)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30519)Memory used [KB]: 1663
% 0.21/0.51  % (30519)Time elapsed: 0.090 s
% 0.21/0.51  % (30519)------------------------------
% 0.21/0.51  % (30519)------------------------------
% 0.21/0.52  % (30534)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f104,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f41,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X3] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X3)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f84,f70])).
% 0.21/0.52  % (30540)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    v1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f50,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f52,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X3] : (k2_relat_1(k7_relat_1(k1_xboole_0,X3)) = k9_relat_1(k1_xboole_0,X3)) )),
% 0.21/0.52    inference(resolution,[],[f53,f66])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,negated_conjecture,(
% 0.21/0.52    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.52    inference(negated_conjecture,[],[f18])).
% 0.21/0.52  fof(f18,conjecture,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f100,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.52    inference(resolution,[],[f56,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 0.21/0.52    inference(backward_demodulation,[],[f82,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(resolution,[],[f95,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  % (30540)Refutation not found, incomplete strategy% (30540)------------------------------
% 0.21/0.52  % (30540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.21/0.52    inference(resolution,[],[f94,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f60,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK1(k1_relat_1(k1_xboole_0)),X0) | v1_xboole_0(k1_relat_1(k1_xboole_0))) )),
% 0.21/0.52    inference(resolution,[],[f93,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(k1_xboole_0)) | r2_hidden(X4,X5)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f92,f70])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(k7_relat_1(k1_xboole_0,X5))) | r2_hidden(X4,X5)) )),
% 0.21/0.52    inference(resolution,[],[f61,f66])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  % (30540)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30540)Memory used [KB]: 1663
% 0.21/0.52  % (30540)Time elapsed: 0.103 s
% 0.21/0.52  % (30540)------------------------------
% 0.21/0.52  % (30540)------------------------------
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    k1_xboole_0 = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))),
% 0.21/0.52    inference(forward_demodulation,[],[f81,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))),
% 0.21/0.52    inference(resolution,[],[f47,f66])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (30526)------------------------------
% 0.21/0.52  % (30526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30526)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (30526)Memory used [KB]: 6268
% 0.21/0.52  % (30526)Time elapsed: 0.095 s
% 0.21/0.52  % (30526)------------------------------
% 0.21/0.52  % (30526)------------------------------
% 0.21/0.52  % (30518)Success in time 0.159 s
%------------------------------------------------------------------------------
