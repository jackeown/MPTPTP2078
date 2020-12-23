%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  58 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 140 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(subsumption_resolution,[],[f43,f18])).

fof(f18,plain,(
    ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2))
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

fof(f43,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f41,plain,(
    ~ r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0) ),
    inference(trivial_inequality_removal,[],[f38])).

fof(f38,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0) ),
    inference(superposition,[],[f28,f37])).

fof(f37,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK2(sK0,k2_relat_1(sK1)),sK2(sK0,k2_relat_1(sK1)),sK2(sK0,k2_relat_1(sK1)))) ),
    inference(resolution,[],[f36,f18])).

fof(f36,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_relat_1(sK1))
      | k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK2(X0,k2_relat_1(sK1)),sK2(X0,k2_relat_1(sK1)),sK2(X0,k2_relat_1(sK1)))) ) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK1))
      | k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(X0,X0,X0)) ) ),
    inference(resolution,[],[f34,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k1_enumset1(X0,X0,X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f29,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f34,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k10_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f21,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f28,plain,(
    ! [X2] :
      ( k1_xboole_0 != k10_relat_1(sK1,k1_enumset1(X2,X2,X2))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(definition_unfolding,[],[f16,f27])).

fof(f16,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2)) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:50:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (6036)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.49  % (6046)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.49  % (6036)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f43,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0)) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1] : ((~r1_tarski(X0,k2_relat_1(X1)) & ! [X2] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X2)) | ~r2_hidden(X2,X0))) & v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f7])).
% 0.22/0.49  fof(f7,conjecture,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.49    inference(resolution,[],[f41,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.22/0.49    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ~r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0)),
% 0.22/0.49    inference(superposition,[],[f28,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK2(sK0,k2_relat_1(sK1)),sK2(sK0,k2_relat_1(sK1)),sK2(sK0,k2_relat_1(sK1))))),
% 0.22/0.49    inference(resolution,[],[f36,f18])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(X0,k2_relat_1(sK1)) | k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(sK2(X0,k2_relat_1(sK1)),sK2(X0,k2_relat_1(sK1)),sK2(X0,k2_relat_1(sK1))))) )),
% 0.22/0.49    inference(resolution,[],[f35,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK1)) | k1_xboole_0 = k10_relat_1(sK1,k1_enumset1(X0,X0,X0))) )),
% 0.22/0.49    inference(resolution,[],[f34,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(X1,k1_enumset1(X0,X0,X0)) | r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f29,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f23,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f19,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_xboole_0(k2_relat_1(sK1),X0) | k1_xboole_0 = k10_relat_1(sK1,X0)) )),
% 0.22/0.49    inference(resolution,[],[f21,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) = k1_xboole_0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2] : (k1_xboole_0 != k10_relat_1(sK1,k1_enumset1(X2,X2,X2)) | ~r2_hidden(X2,sK0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f16,f27])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 != k10_relat_1(sK1,k1_tarski(X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (6036)------------------------------
% 0.22/0.49  % (6036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (6036)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (6036)Memory used [KB]: 6140
% 0.22/0.49  % (6036)Time elapsed: 0.065 s
% 0.22/0.49  % (6036)------------------------------
% 0.22/0.49  % (6036)------------------------------
% 0.22/0.49  % (6029)Success in time 0.129 s
%------------------------------------------------------------------------------
