%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 259 expanded)
%              Number of leaves         :   13 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  107 ( 547 expanded)
%              Number of equality atoms :   45 ( 185 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(subsumption_resolution,[],[f171,f25])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f171,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f168,f159])).

fof(f159,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f70,f152])).

fof(f152,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f147,f83])).

fof(f83,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f72,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f66,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f66,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f61,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f61,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f57,f24])).

fof(f24,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f57,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f23,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f147,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f107,f60])).

fof(f60,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f54,f55])).

fof(f55,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f54,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f21,f26])).

fof(f26,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f21,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f107,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f35,f80])).

fof(f80,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f78,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f78,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f47,f70])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f70,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f66,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f168,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK0),sK0) ),
    inference(backward_demodulation,[],[f167,f155])).

fof(f155,plain,(
    k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f55,f152])).

fof(f167,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,
    ( sK0 != sK0
    | ~ r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(backward_demodulation,[],[f53,f152])).

fof(f53,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | sK0 != sK1 ),
    inference(inner_rewriting,[],[f52])).

fof(f52,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f22,f26])).

fof(f22,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (29132)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (29144)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.50  % (29136)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (29136)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f171,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    ~r1_tarski(k1_xboole_0,sK0)),
% 0.20/0.52    inference(backward_demodulation,[],[f168,f159])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.20/0.52    inference(backward_demodulation,[],[f70,f152])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    sK0 = sK1),
% 0.20/0.52    inference(subsumption_resolution,[],[f147,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    k1_xboole_0 != k4_xboole_0(sK0,sK1) | sK0 = sK1),
% 0.20/0.52    inference(resolution,[],[f72,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 0.20/0.52    inference(resolution,[],[f66,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    r1_tarski(sK1,sK0)),
% 0.20/0.52    inference(resolution,[],[f61,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(equality_resolution,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f57,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f23,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.20/0.52    inference(negated_conjecture,[],[f14])).
% 0.20/0.52  fof(f14,conjecture,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(sK0,sK1) | sK0 = sK1),
% 0.20/0.52    inference(resolution,[],[f107,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | sK0 = sK1),
% 0.20/0.52    inference(backward_demodulation,[],[f54,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.52    inference(resolution,[],[f23,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f21,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    ~r1_tarski(k4_xboole_0(sK0,sK1),sK1) | k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.52    inference(superposition,[],[f35,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.52    inference(forward_demodulation,[],[f78,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0)),
% 0.20/0.52    inference(superposition,[],[f47,f70])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f28,f29,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.20/0.52    inference(resolution,[],[f66,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    ~r1_tarski(k4_xboole_0(sK0,sK0),sK0)),
% 0.20/0.52    inference(backward_demodulation,[],[f167,f155])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0)),
% 0.20/0.52    inference(backward_demodulation,[],[f55,f152])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    ~r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f154])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    sK0 != sK0 | ~r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.20/0.52    inference(backward_demodulation,[],[f53,f152])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | sK0 != sK1),
% 0.20/0.52    inference(inner_rewriting,[],[f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f22,f26])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (29136)------------------------------
% 0.20/0.52  % (29136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29136)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (29136)Memory used [KB]: 1791
% 0.20/0.52  % (29136)Time elapsed: 0.110 s
% 0.20/0.52  % (29136)------------------------------
% 0.20/0.52  % (29136)------------------------------
% 0.20/0.53  % (29113)Success in time 0.173 s
%------------------------------------------------------------------------------
