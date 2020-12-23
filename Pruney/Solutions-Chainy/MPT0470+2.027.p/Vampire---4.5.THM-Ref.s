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
% DateTime   : Thu Dec  3 12:47:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 147 expanded)
%              Number of leaves         :   14 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  177 ( 355 expanded)
%              Number of equality atoms :   47 ( 117 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(subsumption_resolution,[],[f181,f115])).

fof(f115,plain,(
    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f31,f113])).

fof(f113,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f112,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f46,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f112,plain,(
    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f111,f32])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f111,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f110,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f110,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f108,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f108,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f98,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f98,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f97,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f50,f32])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f97,plain,
    ( r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f38,f91])).

fof(f91,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f89,f30])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f88,f64])).

fof(f88,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f87,f32])).

fof(f87,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f86,f36])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f34])).

fof(f34,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f31,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f181,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f180,f64])).

fof(f180,plain,(
    r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f179,f32])).

fof(f179,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f178,f36])).

fof(f178,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f176,f30])).

fof(f176,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f171,f43])).

fof(f171,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f170,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f51,f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f42,f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f170,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f38,f166])).

fof(f166,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f165,f30])).

fof(f165,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(subsumption_resolution,[],[f164,f32])).

fof(f164,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f163,f36])).

fof(f163,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(forward_demodulation,[],[f162,f33])).

fof(f33,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f162,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f160,f35])).

fof(f160,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:21:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (6990)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.46  % (6998)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.48  % (6989)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (6982)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (6984)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (6984)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (6994)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.26/0.51  % (6982)Refutation not found, incomplete strategy% (6982)------------------------------
% 1.26/0.51  % (6982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.51  % (6982)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.51  
% 1.26/0.51  % (6982)Memory used [KB]: 10490
% 1.26/0.51  % (6982)Time elapsed: 0.099 s
% 1.26/0.51  % (6982)------------------------------
% 1.26/0.51  % (6982)------------------------------
% 1.26/0.51  % (6985)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.26/0.51  % (6993)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.26/0.51  % (7006)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.26/0.51  % SZS output start Proof for theBenchmark
% 1.26/0.51  fof(f183,plain,(
% 1.26/0.51    $false),
% 1.26/0.51    inference(subsumption_resolution,[],[f181,f115])).
% 1.26/0.51  fof(f115,plain,(
% 1.26/0.51    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.26/0.51    inference(subsumption_resolution,[],[f31,f113])).
% 1.26/0.51  fof(f113,plain,(
% 1.26/0.51    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.26/0.51    inference(resolution,[],[f112,f64])).
% 1.26/0.51  fof(f64,plain,(
% 1.26/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.26/0.51    inference(resolution,[],[f46,f35])).
% 1.26/0.51  fof(f35,plain,(
% 1.26/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.26/0.51    inference(cnf_transformation,[],[f4])).
% 1.26/0.51  fof(f4,axiom,(
% 1.26/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.26/0.51  fof(f46,plain,(
% 1.26/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.26/0.51    inference(cnf_transformation,[],[f29])).
% 1.26/0.51  fof(f29,plain,(
% 1.26/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.26/0.51    inference(flattening,[],[f28])).
% 1.26/0.51  fof(f28,plain,(
% 1.26/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.26/0.51    inference(nnf_transformation,[],[f3])).
% 1.26/0.51  fof(f3,axiom,(
% 1.26/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.26/0.51  fof(f112,plain,(
% 1.26/0.51    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)),
% 1.26/0.51    inference(subsumption_resolution,[],[f111,f32])).
% 1.26/0.51  fof(f32,plain,(
% 1.26/0.51    v1_xboole_0(k1_xboole_0)),
% 1.26/0.51    inference(cnf_transformation,[],[f1])).
% 1.26/0.51  fof(f1,axiom,(
% 1.26/0.51    v1_xboole_0(k1_xboole_0)),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.26/0.51  fof(f111,plain,(
% 1.26/0.51    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)),
% 1.26/0.51    inference(resolution,[],[f110,f36])).
% 1.26/0.51  fof(f36,plain,(
% 1.26/0.51    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.26/0.51    inference(cnf_transformation,[],[f16])).
% 1.26/0.51  fof(f16,plain,(
% 1.26/0.51    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.26/0.51    inference(ennf_transformation,[],[f7])).
% 1.26/0.51  fof(f7,axiom,(
% 1.26/0.51    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.26/0.51  fof(f110,plain,(
% 1.26/0.51    ~v1_relat_1(k1_xboole_0) | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)),
% 1.26/0.51    inference(subsumption_resolution,[],[f108,f30])).
% 1.26/0.51  fof(f30,plain,(
% 1.26/0.51    v1_relat_1(sK0)),
% 1.26/0.51    inference(cnf_transformation,[],[f27])).
% 1.26/0.51  fof(f27,plain,(
% 1.26/0.51    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.26/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f26])).
% 1.26/0.51  fof(f26,plain,(
% 1.26/0.51    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.26/0.51    introduced(choice_axiom,[])).
% 1.26/0.51  fof(f15,plain,(
% 1.26/0.51    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.26/0.51    inference(ennf_transformation,[],[f14])).
% 1.26/0.51  fof(f14,negated_conjecture,(
% 1.26/0.51    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.26/0.51    inference(negated_conjecture,[],[f13])).
% 1.26/0.51  fof(f13,conjecture,(
% 1.26/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.26/0.51  fof(f108,plain,(
% 1.26/0.51    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 1.26/0.51    inference(resolution,[],[f98,f43])).
% 1.26/0.51  fof(f43,plain,(
% 1.26/0.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.26/0.51    inference(cnf_transformation,[],[f25])).
% 1.26/0.51  fof(f25,plain,(
% 1.26/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.26/0.51    inference(flattening,[],[f24])).
% 1.26/0.51  fof(f24,plain,(
% 1.26/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.26/0.51    inference(ennf_transformation,[],[f8])).
% 1.26/0.51  fof(f8,axiom,(
% 1.26/0.51    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.26/0.51  fof(f98,plain,(
% 1.26/0.51    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | r1_tarski(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)),
% 1.26/0.51    inference(forward_demodulation,[],[f97,f52])).
% 1.26/0.51  fof(f52,plain,(
% 1.26/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.26/0.51    inference(resolution,[],[f50,f32])).
% 1.26/0.51  fof(f50,plain,(
% 1.26/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 1.26/0.51    inference(resolution,[],[f41,f37])).
% 1.26/0.51  fof(f37,plain,(
% 1.26/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.26/0.51    inference(cnf_transformation,[],[f17])).
% 1.26/0.51  fof(f17,plain,(
% 1.26/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.26/0.51    inference(ennf_transformation,[],[f2])).
% 1.26/0.51  fof(f2,axiom,(
% 1.26/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.26/0.51  fof(f41,plain,(
% 1.26/0.51    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 1.26/0.51    inference(cnf_transformation,[],[f22])).
% 1.26/0.51  fof(f22,plain,(
% 1.26/0.51    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.26/0.51    inference(ennf_transformation,[],[f5])).
% 1.26/0.51  fof(f5,axiom,(
% 1.26/0.51    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.26/0.51  fof(f97,plain,(
% 1.26/0.51    r1_tarski(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.26/0.51    inference(superposition,[],[f38,f91])).
% 1.26/0.51  fof(f91,plain,(
% 1.26/0.51    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.26/0.51    inference(resolution,[],[f89,f30])).
% 1.26/0.51  fof(f89,plain,(
% 1.26/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 1.26/0.51    inference(resolution,[],[f88,f64])).
% 1.26/0.51  fof(f88,plain,(
% 1.26/0.51    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.26/0.51    inference(subsumption_resolution,[],[f87,f32])).
% 1.26/0.51  fof(f87,plain,(
% 1.26/0.51    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_xboole_0(k1_xboole_0)) )),
% 1.26/0.51    inference(resolution,[],[f86,f36])).
% 1.26/0.51  fof(f86,plain,(
% 1.26/0.51    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.26/0.51    inference(superposition,[],[f39,f34])).
% 1.26/0.51  fof(f34,plain,(
% 1.26/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.26/0.51    inference(cnf_transformation,[],[f12])).
% 1.26/0.51  fof(f12,axiom,(
% 1.26/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.26/0.51  fof(f39,plain,(
% 1.26/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.26/0.51    inference(cnf_transformation,[],[f19])).
% 1.26/0.51  fof(f19,plain,(
% 1.26/0.51    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.26/0.51    inference(ennf_transformation,[],[f10])).
% 1.26/0.51  fof(f10,axiom,(
% 1.26/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.26/0.51  fof(f38,plain,(
% 1.26/0.51    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.26/0.51    inference(cnf_transformation,[],[f18])).
% 1.26/0.51  fof(f18,plain,(
% 1.26/0.51    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.26/0.51    inference(ennf_transformation,[],[f9])).
% 1.26/0.51  fof(f9,axiom,(
% 1.26/0.51    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.26/0.51  fof(f31,plain,(
% 1.26/0.51    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.26/0.51    inference(cnf_transformation,[],[f27])).
% 1.26/0.51  fof(f181,plain,(
% 1.26/0.51    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.26/0.51    inference(resolution,[],[f180,f64])).
% 1.26/0.51  fof(f180,plain,(
% 1.26/0.51    r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)),
% 1.26/0.51    inference(subsumption_resolution,[],[f179,f32])).
% 1.26/0.51  fof(f179,plain,(
% 1.26/0.51    r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)),
% 1.26/0.51    inference(resolution,[],[f178,f36])).
% 1.26/0.51  fof(f178,plain,(
% 1.26/0.51    ~v1_relat_1(k1_xboole_0) | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)),
% 1.26/0.51    inference(subsumption_resolution,[],[f176,f30])).
% 1.26/0.51  fof(f176,plain,(
% 1.26/0.51    r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0)),
% 1.26/0.51    inference(resolution,[],[f171,f43])).
% 1.26/0.51  fof(f171,plain,(
% 1.26/0.51    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)),
% 1.26/0.51    inference(forward_demodulation,[],[f170,f57])).
% 1.26/0.51  fof(f57,plain,(
% 1.26/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.26/0.51    inference(resolution,[],[f51,f32])).
% 1.26/0.51  fof(f51,plain,(
% 1.26/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.26/0.51    inference(resolution,[],[f42,f37])).
% 1.26/0.51  fof(f42,plain,(
% 1.26/0.51    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.26/0.51    inference(cnf_transformation,[],[f23])).
% 1.26/0.51  fof(f23,plain,(
% 1.26/0.51    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.26/0.51    inference(ennf_transformation,[],[f6])).
% 1.26/0.51  fof(f6,axiom,(
% 1.26/0.51    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.26/0.51  fof(f170,plain,(
% 1.26/0.51    r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.26/0.51    inference(superposition,[],[f38,f166])).
% 1.26/0.51  fof(f166,plain,(
% 1.26/0.51    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.26/0.51    inference(resolution,[],[f165,f30])).
% 1.26/0.51  fof(f165,plain,(
% 1.26/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.26/0.51    inference(subsumption_resolution,[],[f164,f32])).
% 1.26/0.51  fof(f164,plain,(
% 1.26/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_xboole_0(k1_xboole_0)) )),
% 1.26/0.51    inference(resolution,[],[f163,f36])).
% 1.26/0.51  fof(f163,plain,(
% 1.26/0.51    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.26/0.51    inference(forward_demodulation,[],[f162,f33])).
% 1.26/0.51  fof(f33,plain,(
% 1.26/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.26/0.51    inference(cnf_transformation,[],[f12])).
% 1.26/0.51  fof(f162,plain,(
% 1.26/0.51    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.26/0.51    inference(subsumption_resolution,[],[f160,f35])).
% 1.26/0.51  fof(f160,plain,(
% 1.26/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.26/0.51    inference(superposition,[],[f40,f34])).
% 1.26/0.51  fof(f40,plain,(
% 1.26/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.26/0.51    inference(cnf_transformation,[],[f21])).
% 1.26/0.51  fof(f21,plain,(
% 1.26/0.51    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.26/0.51    inference(flattening,[],[f20])).
% 1.26/0.51  fof(f20,plain,(
% 1.26/0.51    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.26/0.51    inference(ennf_transformation,[],[f11])).
% 1.26/0.51  fof(f11,axiom,(
% 1.26/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.26/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.26/0.51  % SZS output end Proof for theBenchmark
% 1.26/0.51  % (6984)------------------------------
% 1.26/0.51  % (6984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.51  % (6984)Termination reason: Refutation
% 1.26/0.51  
% 1.26/0.51  % (6984)Memory used [KB]: 6268
% 1.26/0.51  % (6984)Time elapsed: 0.105 s
% 1.26/0.51  % (6984)------------------------------
% 1.26/0.51  % (6984)------------------------------
% 1.26/0.51  % (6988)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.26/0.52  % (6980)Success in time 0.161 s
%------------------------------------------------------------------------------
