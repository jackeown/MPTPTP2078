%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  51 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 105 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f50,f66])).

% (15934)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
fof(f66,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f64,f23])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f64,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK0),sK1)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f63,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f63,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | ~ r1_tarski(k4_xboole_0(sK1,sK0),sK1)
    | spl2_2 ),
    inference(resolution,[],[f56,f51])).

fof(f51,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1))
    | spl2_2 ),
    inference(resolution,[],[f46,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f46,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_2
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f55,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f55,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(X8,k2_xboole_0(X9,X10))
      | r1_tarski(X8,k5_xboole_0(X9,X10))
      | ~ r1_xboole_0(X8,X9) ) ),
    inference(resolution,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,k5_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f50,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f48,f24])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f48,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(resolution,[],[f42,f25])).

fof(f42,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_1
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f38,f44,f40])).

fof(f38,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f21,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f21,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:37:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (15919)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % (15926)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.47  % (15926)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f47,f50,f66])).
% 0.21/0.48  % (15934)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    $false | spl2_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ~r1_tarski(k4_xboole_0(sK1,sK0),sK1) | spl2_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f63,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~r1_xboole_0(k4_xboole_0(sK1,sK0),sK0) | ~r1_tarski(k4_xboole_0(sK1,sK0),sK1) | spl2_2),
% 0.21/0.48    inference(resolution,[],[f56,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ~r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)) | spl2_2),
% 0.21/0.48    inference(resolution,[],[f46,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl2_2 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X2)) )),
% 0.21/0.48    inference(resolution,[],[f55,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X10,X8,X9] : (~r1_tarski(X8,k2_xboole_0(X9,X10)) | r1_tarski(X8,k5_xboole_0(X9,X10)) | ~r1_xboole_0(X8,X9)) )),
% 0.21/0.48    inference(resolution,[],[f30,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    $false | spl2_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f48,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) | spl2_1),
% 0.21/0.48    inference(resolution,[],[f42,f25])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl2_1 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ~spl2_1 | ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f44,f40])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    inference(resolution,[],[f21,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (15926)------------------------------
% 0.21/0.48  % (15926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15926)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (15926)Memory used [KB]: 5373
% 0.21/0.48  % (15926)Time elapsed: 0.063 s
% 0.21/0.48  % (15926)------------------------------
% 0.21/0.48  % (15926)------------------------------
% 0.21/0.48  % (15917)Success in time 0.117 s
%------------------------------------------------------------------------------
