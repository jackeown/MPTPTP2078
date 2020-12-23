%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:34 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   44 (  57 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :   15
%              Number of atoms          :   97 ( 148 expanded)
%              Number of equality atoms :   20 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(subsumption_resolution,[],[f71,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

% (17893)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f71,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f66,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f66,plain,(
    ! [X0] : r1_tarski(sK0,X0) ),
    inference(resolution,[],[f61,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f61,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(resolution,[],[f60,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f60,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f59,plain,
    ( ~ r1_tarski(sK0,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f55,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f55,plain,(
    r1_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f53,f22])).

fof(f22,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | r1_xboole_0(X0,sK0) ) ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f48,plain,(
    r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(superposition,[],[f46,f23])).

fof(f23,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 != k10_relat_1(sK1,X0)
      | r1_xboole_0(k2_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_vampire %s %d
% 0.16/0.35  % Computer   : n002.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % WCLimit    : 600
% 0.16/0.35  % DateTime   : Tue Dec  1 11:02:07 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.23/0.51  % (17902)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.51  % (17894)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.14/0.52  % (17886)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.14/0.52  % (17902)Refutation not found, incomplete strategy% (17902)------------------------------
% 1.14/0.52  % (17902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.52  % (17902)Termination reason: Refutation not found, incomplete strategy
% 1.14/0.52  
% 1.14/0.52  % (17902)Memory used [KB]: 10746
% 1.14/0.52  % (17902)Time elapsed: 0.067 s
% 1.14/0.52  % (17902)------------------------------
% 1.14/0.52  % (17902)------------------------------
% 1.14/0.52  % (17886)Refutation found. Thanks to Tanya!
% 1.14/0.52  % SZS status Theorem for theBenchmark
% 1.14/0.52  % SZS output start Proof for theBenchmark
% 1.14/0.52  fof(f73,plain,(
% 1.14/0.52    $false),
% 1.14/0.52    inference(subsumption_resolution,[],[f71,f21])).
% 1.14/0.52  fof(f21,plain,(
% 1.14/0.52    k1_xboole_0 != sK0),
% 1.14/0.52    inference(cnf_transformation,[],[f12])).
% 1.14/0.52  fof(f12,plain,(
% 1.14/0.52    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 1.14/0.52    inference(flattening,[],[f11])).
% 1.14/0.52  fof(f11,plain,(
% 1.14/0.52    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 1.14/0.52    inference(ennf_transformation,[],[f9])).
% 1.14/0.52  % (17893)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.14/0.52  fof(f9,negated_conjecture,(
% 1.14/0.52    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.14/0.52    inference(negated_conjecture,[],[f8])).
% 1.14/0.52  fof(f8,conjecture,(
% 1.14/0.52    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.14/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 1.14/0.52  fof(f71,plain,(
% 1.14/0.52    k1_xboole_0 = sK0),
% 1.14/0.52    inference(resolution,[],[f66,f40])).
% 1.14/0.52  fof(f40,plain,(
% 1.14/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.14/0.52    inference(resolution,[],[f31,f24])).
% 1.14/0.52  fof(f24,plain,(
% 1.14/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f4])).
% 1.14/0.52  fof(f4,axiom,(
% 1.14/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.14/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.14/0.52  fof(f31,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.14/0.52    inference(cnf_transformation,[],[f3])).
% 1.14/0.52  fof(f3,axiom,(
% 1.14/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.14/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.14/0.52  fof(f66,plain,(
% 1.14/0.52    ( ! [X0] : (r1_tarski(sK0,X0)) )),
% 1.14/0.52    inference(resolution,[],[f61,f33])).
% 1.14/0.52  fof(f33,plain,(
% 1.14/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f17])).
% 1.14/0.52  fof(f17,plain,(
% 1.14/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.14/0.52    inference(ennf_transformation,[],[f2])).
% 1.14/0.52  fof(f2,axiom,(
% 1.14/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.14/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.14/0.52  fof(f61,plain,(
% 1.14/0.52    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.14/0.52    inference(resolution,[],[f60,f25])).
% 1.14/0.52  fof(f25,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f13])).
% 1.14/0.52  fof(f13,plain,(
% 1.14/0.52    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.14/0.52    inference(ennf_transformation,[],[f10])).
% 1.14/0.52  fof(f10,plain,(
% 1.14/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.14/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 1.14/0.52  fof(f1,axiom,(
% 1.14/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.14/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.14/0.52  fof(f60,plain,(
% 1.14/0.52    v1_xboole_0(sK0)),
% 1.14/0.52    inference(subsumption_resolution,[],[f59,f36])).
% 1.14/0.52  fof(f36,plain,(
% 1.14/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.14/0.52    inference(equality_resolution,[],[f30])).
% 1.14/0.52  fof(f30,plain,(
% 1.14/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.14/0.52    inference(cnf_transformation,[],[f3])).
% 1.14/0.52  fof(f59,plain,(
% 1.14/0.52    ~r1_tarski(sK0,sK0) | v1_xboole_0(sK0)),
% 1.14/0.52    inference(resolution,[],[f55,f26])).
% 1.14/0.52  fof(f26,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f15])).
% 1.14/0.52  fof(f15,plain,(
% 1.14/0.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.14/0.52    inference(flattening,[],[f14])).
% 1.14/0.52  fof(f14,plain,(
% 1.14/0.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.14/0.52    inference(ennf_transformation,[],[f6])).
% 1.14/0.52  fof(f6,axiom,(
% 1.14/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.14/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.14/0.52  fof(f55,plain,(
% 1.14/0.52    r1_xboole_0(sK0,sK0)),
% 1.14/0.52    inference(resolution,[],[f53,f22])).
% 1.14/0.52  fof(f22,plain,(
% 1.14/0.52    r1_tarski(sK0,k2_relat_1(sK1))),
% 1.14/0.52    inference(cnf_transformation,[],[f12])).
% 1.14/0.52  fof(f53,plain,(
% 1.14/0.52    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | r1_xboole_0(X0,sK0)) )),
% 1.14/0.52    inference(resolution,[],[f48,f35])).
% 1.14/0.52  fof(f35,plain,(
% 1.14/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1) | r1_xboole_0(X0,X2)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f19])).
% 1.14/0.52  fof(f19,plain,(
% 1.14/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.14/0.52    inference(flattening,[],[f18])).
% 1.14/0.52  fof(f18,plain,(
% 1.14/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.14/0.52    inference(ennf_transformation,[],[f5])).
% 1.14/0.52  fof(f5,axiom,(
% 1.14/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.14/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.14/0.52  fof(f48,plain,(
% 1.14/0.52    r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.14/0.52    inference(trivial_inequality_removal,[],[f47])).
% 1.14/0.52  fof(f47,plain,(
% 1.14/0.52    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.14/0.52    inference(superposition,[],[f46,f23])).
% 1.14/0.52  fof(f23,plain,(
% 1.14/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.14/0.52    inference(cnf_transformation,[],[f12])).
% 1.14/0.52  fof(f46,plain,(
% 1.14/0.52    ( ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | r1_xboole_0(k2_relat_1(sK1),X0)) )),
% 1.14/0.52    inference(resolution,[],[f28,f20])).
% 1.14/0.52  fof(f20,plain,(
% 1.14/0.52    v1_relat_1(sK1)),
% 1.14/0.52    inference(cnf_transformation,[],[f12])).
% 1.14/0.52  fof(f28,plain,(
% 1.14/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) )),
% 1.14/0.52    inference(cnf_transformation,[],[f16])).
% 1.14/0.52  fof(f16,plain,(
% 1.14/0.52    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.14/0.52    inference(ennf_transformation,[],[f7])).
% 1.14/0.52  fof(f7,axiom,(
% 1.14/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.14/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 1.14/0.52  % SZS output end Proof for theBenchmark
% 1.14/0.52  % (17886)------------------------------
% 1.14/0.52  % (17886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.52  % (17886)Termination reason: Refutation
% 1.14/0.52  
% 1.14/0.52  % (17886)Memory used [KB]: 6140
% 1.14/0.52  % (17886)Time elapsed: 0.073 s
% 1.14/0.52  % (17886)------------------------------
% 1.14/0.52  % (17886)------------------------------
% 1.14/0.53  % (17879)Success in time 0.154 s
%------------------------------------------------------------------------------
