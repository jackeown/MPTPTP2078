%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 205 expanded)
%              Number of leaves         :    8 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 445 expanded)
%              Number of equality atoms :   41 ( 151 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(global_subsumption,[],[f89,f94])).

fof(f94,plain,(
    r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f48,f69])).

fof(f69,plain,(
    k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k11_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f18,f19,f66,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f66,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f55,f65])).

fof(f65,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(global_subsumption,[],[f18,f64])).

fof(f64,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f63,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f63,plain,(
    ~ r1_tarski(k11_relat_1(sK1,sK0),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f58,f61])).

fof(f61,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_enumset1(X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f18,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f22,f37])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f58,plain,(
    ~ r1_tarski(k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f38,f56])).

fof(f56,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f18,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f38,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f20,f37,f37])).

fof(f20,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

fof(f55,plain,(
    ! [X2,X0,X1] : r1_tarski(k1_xboole_0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X2,X0,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) != X3
      | r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,(
    ~ r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f63,f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:08:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (4908)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (4902)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (4916)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (4916)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (4902)Refutation not found, incomplete strategy% (4902)------------------------------
% 0.21/0.53  % (4902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4893)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(global_subsumption,[],[f89,f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0))),
% 0.21/0.54    inference(superposition,[],[f48,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k11_relat_1(sK1,sK0)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f18,f19,f66,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f27,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f21,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f55,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.54    inference(global_subsumption,[],[f18,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | ~v1_relat_1(sK1) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.54    inference(superposition,[],[f63,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1) | r2_hidden(X0,k1_relat_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ~r1_tarski(k11_relat_1(sK1,sK0),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.21/0.54    inference(backward_demodulation,[],[f58,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_enumset1(X0,X0,X0))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f18,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f22,f37])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ~r1_tarski(k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.21/0.54    inference(backward_demodulation,[],[f38,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f18,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.21/0.54    inference(definition_unfolding,[],[f20,f37,f37])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.54    inference(negated_conjecture,[],[f8])).
% 0.21/0.54  fof(f8,conjecture,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k1_xboole_0,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.54    inference(equality_resolution,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    v1_funct_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2))) )),
% 0.21/0.54    inference(equality_resolution,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) != X3 | r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ~r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0))),
% 0.21/0.54    inference(backward_demodulation,[],[f63,f69])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (4916)------------------------------
% 0.21/0.54  % (4916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4916)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (4916)Memory used [KB]: 6268
% 0.21/0.54  % (4916)Time elapsed: 0.114 s
% 0.21/0.54  % (4916)------------------------------
% 0.21/0.54  % (4916)------------------------------
% 0.21/0.54  % (4894)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (4902)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4902)Memory used [KB]: 10618
% 0.21/0.54  % (4902)Time elapsed: 0.115 s
% 0.21/0.54  % (4902)------------------------------
% 0.21/0.54  % (4902)------------------------------
% 0.21/0.54  % (4897)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (4891)Success in time 0.174 s
%------------------------------------------------------------------------------
