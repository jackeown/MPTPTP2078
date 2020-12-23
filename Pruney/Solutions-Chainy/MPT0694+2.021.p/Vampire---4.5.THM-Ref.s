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
% DateTime   : Thu Dec  3 12:54:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 177 expanded)
%              Number of leaves         :   10 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 433 expanded)
%              Number of equality atoms :   18 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f574,plain,(
    $false ),
    inference(subsumption_resolution,[],[f572,f362])).

fof(f362,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0)) ),
    inference(superposition,[],[f260,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f260,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0)) ),
    inference(backward_demodulation,[],[f71,f259])).

fof(f259,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f249,f54])).

fof(f54,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f24,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

fof(f249,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f55,f131])).

fof(f131,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f24,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f55,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(unit_resulting_resolution,[],[f36,f30])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f24,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0)) ),
    inference(backward_demodulation,[],[f42,f54])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k2_relat_1(k7_relat_1(sK2,X0))) ),
    inference(unit_resulting_resolution,[],[f36,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f572,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) ),
    inference(superposition,[],[f366,f550])).

fof(f550,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f24,f25,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f366,plain,(
    ! [X0] : ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f360,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f360,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f35,f260,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f35,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))) ),
    inference(backward_demodulation,[],[f26,f27])).

fof(f26,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:16:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (15194)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.43  % (15192)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.44  % (15196)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.44  % (15190)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.44  % (15189)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.45  % (15195)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.45  % (15188)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.46  % (15190)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f574,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f572,f362])).
% 0.20/0.46  fof(f362,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X1,X0)),k9_relat_1(sK2,X0))) )),
% 0.20/0.46    inference(superposition,[],[f260,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.46  fof(f260,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0))) )),
% 0.20/0.46    inference(backward_demodulation,[],[f71,f259])).
% 0.20/0.46  fof(f259,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f249,f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0] : (k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0))) )),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f24,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    v1_relat_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.46    inference(flattening,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.20/0.46    inference(negated_conjecture,[],[f9])).
% 0.20/0.46  fof(f9,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).
% 0.20/0.46  fof(f249,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1)))) )),
% 0.20/0.46    inference(backward_demodulation,[],[f55,f131])).
% 0.20/0.46  fof(f131,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f24,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f36,f30])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f24,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0))) )),
% 0.20/0.46    inference(backward_demodulation,[],[f42,f54])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k2_relat_1(k7_relat_1(sK2,X0)))) )),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f36,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.20/0.46  fof(f572,plain,(
% 0.20/0.46    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))),
% 0.20/0.46    inference(superposition,[],[f366,f550])).
% 0.20/0.46  fof(f550,plain,(
% 0.20/0.46    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) )),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f24,f25,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    v1_funct_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f366,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,X0))) )),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f360,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.20/0.46  fof(f360,plain,(
% 0.20/0.46    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f35,f260,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),
% 0.20/0.46    inference(backward_demodulation,[],[f26,f27])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (15190)------------------------------
% 0.20/0.46  % (15190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (15190)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (15190)Memory used [KB]: 6524
% 0.20/0.46  % (15190)Time elapsed: 0.024 s
% 0.20/0.46  % (15190)------------------------------
% 0.20/0.46  % (15190)------------------------------
% 0.20/0.46  % (15181)Success in time 0.114 s
%------------------------------------------------------------------------------
