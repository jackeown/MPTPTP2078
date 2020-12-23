%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  88 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f44,f44,f59,f50])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f59,plain,(
    ~ r2_hidden(sK0,k3_tarski(k1_enumset1(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(unit_resulting_resolution,[],[f20,f54,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f54,plain,(
    r1_tarski(k3_tarski(k1_enumset1(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))),sK1) ),
    inference(forward_demodulation,[],[f53,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f53,plain,(
    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0))),sK1) ),
    inference(forward_demodulation,[],[f42,f32])).

fof(f42,plain,(
    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f19,f41,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f30,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f19,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f20,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k1_enumset1(X0,X1,X4)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:44:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (26858)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (26882)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (26874)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (26862)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (26862)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (26874)Refutation not found, incomplete strategy% (26874)------------------------------
% 0.21/0.55  % (26874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26874)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26874)Memory used [KB]: 1663
% 0.21/0.55  % (26874)Time elapsed: 0.144 s
% 0.21/0.55  % (26874)------------------------------
% 0.21/0.55  % (26874)------------------------------
% 0.21/0.55  % (26865)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (26853)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.56  % (26855)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.56  % SZS output start Proof for theBenchmark
% 1.41/0.56  fof(f116,plain,(
% 1.41/0.56    $false),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f44,f44,f59,f50])).
% 1.41/0.56  fof(f50,plain,(
% 1.41/0.56    ( ! [X2,X0,X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,k3_tarski(X0))) )),
% 1.41/0.56    inference(equality_resolution,[],[f38])).
% 1.41/0.56  fof(f38,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 1.41/0.56    inference(cnf_transformation,[],[f11])).
% 1.41/0.56  fof(f11,axiom,(
% 1.41/0.56    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 1.41/0.56  fof(f59,plain,(
% 1.41/0.56    ~r2_hidden(sK0,k3_tarski(k1_enumset1(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))))),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f20,f54,f29])).
% 1.41/0.56  fof(f29,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f18])).
% 1.41/0.56  fof(f18,plain,(
% 1.41/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.41/0.56    inference(ennf_transformation,[],[f15])).
% 1.41/0.56  fof(f15,plain,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.41/0.56  fof(f1,axiom,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.56  fof(f54,plain,(
% 1.41/0.56    r1_tarski(k3_tarski(k1_enumset1(sK1,k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))),sK1)),
% 1.41/0.56    inference(forward_demodulation,[],[f53,f32])).
% 1.41/0.56  fof(f32,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f3])).
% 1.41/0.56  fof(f3,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 1.41/0.56  fof(f53,plain,(
% 1.41/0.56    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),sK1,k1_enumset1(sK0,sK0,sK0))),sK1)),
% 1.41/0.56    inference(forward_demodulation,[],[f42,f32])).
% 1.41/0.56  fof(f42,plain,(
% 1.41/0.56    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),sK1)),sK1)),
% 1.41/0.56    inference(definition_unfolding,[],[f19,f41,f40])).
% 1.41/0.56  fof(f40,plain,(
% 1.41/0.56    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.41/0.56    inference(definition_unfolding,[],[f31,f39])).
% 1.41/0.56  fof(f39,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f5])).
% 1.41/0.56  fof(f5,axiom,(
% 1.41/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.56  fof(f31,plain,(
% 1.41/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f4])).
% 1.41/0.56  fof(f4,axiom,(
% 1.41/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.56  fof(f41,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.41/0.56    inference(definition_unfolding,[],[f30,f39])).
% 1.41/0.56  fof(f30,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f12])).
% 1.41/0.56  fof(f12,axiom,(
% 1.41/0.56    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.41/0.56  fof(f19,plain,(
% 1.41/0.56    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 1.41/0.56    inference(cnf_transformation,[],[f16])).
% 1.41/0.56  fof(f16,plain,(
% 1.41/0.56    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 1.41/0.56    inference(ennf_transformation,[],[f14])).
% 1.41/0.56  fof(f14,negated_conjecture,(
% 1.41/0.56    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 1.41/0.56    inference(negated_conjecture,[],[f13])).
% 1.41/0.56  fof(f13,conjecture,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 1.41/0.56  fof(f20,plain,(
% 1.41/0.56    ~r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(cnf_transformation,[],[f16])).
% 1.41/0.56  fof(f44,plain,(
% 1.41/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_enumset1(X0,X1,X4))) )),
% 1.41/0.56    inference(equality_resolution,[],[f43])).
% 1.41/0.56  fof(f43,plain,(
% 1.41/0.56    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X0,X1,X4) != X3) )),
% 1.41/0.56    inference(equality_resolution,[],[f28])).
% 1.41/0.56  fof(f28,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.41/0.56    inference(cnf_transformation,[],[f17])).
% 1.41/0.56  fof(f17,plain,(
% 1.41/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.41/0.56    inference(ennf_transformation,[],[f2])).
% 1.41/0.56  fof(f2,axiom,(
% 1.41/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.41/0.56  % SZS output end Proof for theBenchmark
% 1.41/0.56  % (26862)------------------------------
% 1.41/0.56  % (26862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (26862)Termination reason: Refutation
% 1.41/0.56  
% 1.41/0.56  % (26862)Memory used [KB]: 10746
% 1.41/0.56  % (26862)Time elapsed: 0.115 s
% 1.41/0.56  % (26862)------------------------------
% 1.41/0.56  % (26862)------------------------------
% 1.41/0.56  % (26852)Success in time 0.198 s
%------------------------------------------------------------------------------
