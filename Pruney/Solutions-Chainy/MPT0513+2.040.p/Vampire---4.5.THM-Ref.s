%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:49 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 (  62 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f33,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK1(k1_xboole_0)),k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f30,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f31,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f27,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f25,f19])).

fof(f19,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | k2_xboole_0(k1_tarski(sK1(X0)),X0) = X0 ) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f18,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (790003712)
% 0.13/0.39  ipcrm: permission denied for id (790036501)
% 0.20/0.44  ipcrm: permission denied for id (790102085)
% 0.20/0.46  ipcrm: permission denied for id (790134871)
% 0.20/0.57  % (26322)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.57  % (26322)Refutation not found, incomplete strategy% (26322)------------------------------
% 0.20/0.57  % (26322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (26322)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (26322)Memory used [KB]: 1535
% 0.20/0.57  % (26322)Time elapsed: 0.003 s
% 0.20/0.57  % (26322)------------------------------
% 0.20/0.57  % (26322)------------------------------
% 0.20/0.60  % (26309)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.60  % (26309)Refutation not found, incomplete strategy% (26309)------------------------------
% 0.20/0.60  % (26309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (26309)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (26309)Memory used [KB]: 6012
% 0.20/0.60  % (26309)Time elapsed: 0.038 s
% 0.20/0.60  % (26309)------------------------------
% 0.20/0.60  % (26309)------------------------------
% 0.98/0.62  % (26318)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.98/0.62  % (26324)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.98/0.62  % (26324)Refutation not found, incomplete strategy% (26324)------------------------------
% 0.98/0.62  % (26324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.98/0.62  % (26324)Termination reason: Refutation not found, incomplete strategy
% 0.98/0.62  
% 0.98/0.62  % (26324)Memory used [KB]: 6012
% 0.98/0.62  % (26324)Time elapsed: 0.066 s
% 0.98/0.62  % (26324)------------------------------
% 0.98/0.62  % (26324)------------------------------
% 0.98/0.62  % (26326)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.98/0.63  % (26326)Refutation found. Thanks to Tanya!
% 0.98/0.63  % SZS status Theorem for theBenchmark
% 0.98/0.63  % SZS output start Proof for theBenchmark
% 0.98/0.63  fof(f35,plain,(
% 0.98/0.63    $false),
% 0.98/0.63    inference(subsumption_resolution,[],[f18,f34])).
% 0.98/0.63  fof(f34,plain,(
% 0.98/0.63    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.98/0.63    inference(subsumption_resolution,[],[f33,f24])).
% 0.98/0.63  fof(f24,plain,(
% 0.98/0.63    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.98/0.63    inference(cnf_transformation,[],[f4])).
% 0.98/0.63  fof(f4,axiom,(
% 0.98/0.63    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.98/0.63  fof(f33,plain,(
% 0.98/0.63    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k1_tarski(sK1(k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.98/0.63    inference(resolution,[],[f30,f32])).
% 0.98/0.63  fof(f32,plain,(
% 0.98/0.63    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.98/0.63    inference(subsumption_resolution,[],[f31,f29])).
% 0.98/0.63  fof(f29,plain,(
% 0.98/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.98/0.63    inference(trivial_inequality_removal,[],[f28])).
% 0.98/0.63  fof(f28,plain,(
% 0.98/0.63    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) )),
% 0.98/0.63    inference(superposition,[],[f27,f21])).
% 0.98/0.63  fof(f21,plain,(
% 0.98/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.98/0.63    inference(cnf_transformation,[],[f2])).
% 0.98/0.63  fof(f2,axiom,(
% 0.98/0.63    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.98/0.63  fof(f27,plain,(
% 0.98/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.98/0.63    inference(cnf_transformation,[],[f17])).
% 0.98/0.63  fof(f17,plain,(
% 0.98/0.63    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.98/0.63    inference(ennf_transformation,[],[f11])).
% 0.98/0.63  fof(f11,plain,(
% 0.98/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 0.98/0.63    inference(unused_predicate_definition_removal,[],[f1])).
% 0.98/0.63  fof(f1,axiom,(
% 0.98/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.98/0.63  fof(f31,plain,(
% 0.98/0.63    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.98/0.63    inference(superposition,[],[f25,f19])).
% 0.98/0.63  fof(f19,plain,(
% 0.98/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.98/0.63    inference(cnf_transformation,[],[f6])).
% 0.98/0.63  fof(f6,axiom,(
% 0.98/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.98/0.63  fof(f25,plain,(
% 0.98/0.63    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.98/0.63    inference(cnf_transformation,[],[f15])).
% 0.98/0.63  fof(f15,plain,(
% 0.98/0.63    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.98/0.63    inference(flattening,[],[f14])).
% 0.98/0.63  fof(f14,plain,(
% 0.98/0.63    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.98/0.63    inference(ennf_transformation,[],[f7])).
% 0.98/0.63  fof(f7,axiom,(
% 0.98/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.98/0.63  fof(f30,plain,(
% 0.98/0.63    ( ! [X0] : (v1_relat_1(X0) | k2_xboole_0(k1_tarski(sK1(X0)),X0) = X0) )),
% 0.98/0.63    inference(resolution,[],[f26,f22])).
% 0.98/0.63  fof(f22,plain,(
% 0.98/0.63    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 0.98/0.63    inference(cnf_transformation,[],[f13])).
% 0.98/0.63  fof(f13,plain,(
% 0.98/0.63    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.98/0.63    inference(ennf_transformation,[],[f10])).
% 0.98/0.63  fof(f10,plain,(
% 0.98/0.63    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.98/0.63    inference(unused_predicate_definition_removal,[],[f5])).
% 0.98/0.63  fof(f5,axiom,(
% 0.98/0.63    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.98/0.63  fof(f26,plain,(
% 0.98/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.98/0.63    inference(cnf_transformation,[],[f16])).
% 0.98/0.63  fof(f16,plain,(
% 0.98/0.63    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.98/0.63    inference(ennf_transformation,[],[f3])).
% 0.98/0.63  fof(f3,axiom,(
% 0.98/0.63    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.98/0.63  fof(f18,plain,(
% 0.98/0.63    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.98/0.63    inference(cnf_transformation,[],[f12])).
% 0.98/0.63  fof(f12,plain,(
% 0.98/0.63    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.98/0.63    inference(ennf_transformation,[],[f9])).
% 0.98/0.63  fof(f9,negated_conjecture,(
% 0.98/0.63    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.98/0.63    inference(negated_conjecture,[],[f8])).
% 0.98/0.63  fof(f8,conjecture,(
% 0.98/0.63    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.98/0.63  % SZS output end Proof for theBenchmark
% 0.98/0.63  % (26326)------------------------------
% 0.98/0.63  % (26326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.98/0.63  % (26326)Termination reason: Refutation
% 0.98/0.63  
% 0.98/0.63  % (26326)Memory used [KB]: 1663
% 0.98/0.63  % (26326)Time elapsed: 0.083 s
% 0.98/0.63  % (26326)------------------------------
% 0.98/0.63  % (26326)------------------------------
% 0.98/0.63  % (26175)Success in time 0.271 s
%------------------------------------------------------------------------------
