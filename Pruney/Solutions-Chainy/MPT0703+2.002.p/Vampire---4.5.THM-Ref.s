%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:18 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 133 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  140 ( 499 expanded)
%              Number of equality atoms :   33 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f858,plain,(
    $false ),
    inference(subsumption_resolution,[],[f844,f42])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f844,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(superposition,[],[f70,f763])).

fof(f763,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(forward_demodulation,[],[f762,f85])).

fof(f85,plain,(
    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f25,f27,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f27,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

% (7259)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f762,plain,(
    k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f761,f24])).

fof(f761,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f760,f25])).

fof(f760,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f743,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(sK0,X0)),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f39,f27,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

% (7257)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f743,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f33,f210])).

fof(f210,plain,(
    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f209,f24])).

fof(f209,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f201,f25])).

% (7252)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f201,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f74,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f37,f31,f31])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

fof(f74,plain,(
    k10_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f26,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f26,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X0] : ~ r1_tarski(sK0,k1_setfam_1(k2_tarski(X0,sK1))) ),
    inference(unit_resulting_resolution,[],[f44,f28,f38])).

fof(f28,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f39,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:03:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (7254)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (7236)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (7255)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (7237)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (7244)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (7247)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (7239)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (7260)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (7245)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (7233)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.58/0.56  % (7235)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.58/0.56  % (7238)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.57  % (7236)Refutation found. Thanks to Tanya!
% 1.58/0.57  % SZS status Theorem for theBenchmark
% 1.58/0.57  % SZS output start Proof for theBenchmark
% 1.58/0.57  fof(f858,plain,(
% 1.58/0.57    $false),
% 1.58/0.57    inference(subsumption_resolution,[],[f844,f42])).
% 1.58/0.57  fof(f42,plain,(
% 1.58/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.58/0.57    inference(equality_resolution,[],[f35])).
% 1.58/0.57  fof(f35,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.58/0.57    inference(cnf_transformation,[],[f23])).
% 1.58/0.57  fof(f23,plain,(
% 1.58/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.58/0.57    inference(flattening,[],[f22])).
% 1.58/0.57  fof(f22,plain,(
% 1.58/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.58/0.57    inference(nnf_transformation,[],[f1])).
% 1.58/0.57  fof(f1,axiom,(
% 1.58/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.58/0.57  fof(f844,plain,(
% 1.58/0.57    ~r1_tarski(sK0,sK0)),
% 1.58/0.57    inference(superposition,[],[f70,f763])).
% 1.58/0.57  fof(f763,plain,(
% 1.58/0.57    sK0 = k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.58/0.57    inference(forward_demodulation,[],[f762,f85])).
% 1.58/0.57  fof(f85,plain,(
% 1.58/0.57    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f24,f25,f27,f33])).
% 1.58/0.57  fof(f33,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f15])).
% 1.58/0.57  fof(f15,plain,(
% 1.58/0.57    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(flattening,[],[f14])).
% 1.58/0.57  fof(f14,plain,(
% 1.58/0.57    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f8])).
% 1.58/0.57  fof(f8,axiom,(
% 1.58/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.58/0.57  fof(f27,plain,(
% 1.58/0.57    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.58/0.57    inference(cnf_transformation,[],[f21])).
% 1.58/0.57  fof(f21,plain,(
% 1.58/0.57    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).
% 1.58/0.57  fof(f20,plain,(
% 1.58/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f12,plain,(
% 1.58/0.57    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.58/0.57    inference(flattening,[],[f11])).
% 1.58/0.57  fof(f11,plain,(
% 1.58/0.57    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.58/0.57    inference(ennf_transformation,[],[f10])).
% 1.58/0.57  fof(f10,negated_conjecture,(
% 1.58/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.58/0.57    inference(negated_conjecture,[],[f9])).
% 1.58/0.57  fof(f9,conjecture,(
% 1.58/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 1.58/0.57  fof(f25,plain,(
% 1.58/0.57    v1_funct_1(sK2)),
% 1.58/0.57    inference(cnf_transformation,[],[f21])).
% 1.58/0.57  fof(f24,plain,(
% 1.58/0.57    v1_relat_1(sK2)),
% 1.58/0.57    inference(cnf_transformation,[],[f21])).
% 1.58/0.57  % (7259)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.58/0.57  fof(f762,plain,(
% 1.58/0.57    k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.58/0.57    inference(subsumption_resolution,[],[f761,f24])).
% 1.58/0.57  fof(f761,plain,(
% 1.58/0.57    k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k2_tarski(sK0,sK1)) | ~v1_relat_1(sK2)),
% 1.58/0.57    inference(subsumption_resolution,[],[f760,f25])).
% 1.58/0.57  fof(f760,plain,(
% 1.58/0.57    k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k2_tarski(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.58/0.57    inference(subsumption_resolution,[],[f743,f64])).
% 1.58/0.57  fof(f64,plain,(
% 1.58/0.57    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(sK0,X0)),k2_relat_1(sK2))) )),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f39,f27,f38])).
% 1.58/0.57  fof(f38,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f19])).
% 1.58/0.57  fof(f19,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.58/0.57    inference(flattening,[],[f18])).
% 1.58/0.57  % (7257)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.58/0.57  fof(f18,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f3])).
% 1.58/0.57  fof(f3,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.58/0.57  fof(f39,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 1.58/0.57    inference(definition_unfolding,[],[f29,f31])).
% 1.58/0.57  fof(f31,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f6])).
% 1.58/0.57  fof(f6,axiom,(
% 1.58/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.58/0.57  fof(f29,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f2])).
% 1.58/0.57  fof(f2,axiom,(
% 1.58/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.58/0.57  fof(f743,plain,(
% 1.58/0.57    k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k1_setfam_1(k2_tarski(sK0,sK1)) | ~r1_tarski(k1_setfam_1(k2_tarski(sK0,sK1)),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.58/0.57    inference(superposition,[],[f33,f210])).
% 1.58/0.57  fof(f210,plain,(
% 1.58/0.57    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))),
% 1.58/0.57    inference(subsumption_resolution,[],[f209,f24])).
% 1.58/0.57  fof(f209,plain,(
% 1.58/0.57    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) | ~v1_relat_1(sK2)),
% 1.58/0.57    inference(subsumption_resolution,[],[f201,f25])).
% 1.58/0.57  % (7252)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.58/0.57  fof(f201,plain,(
% 1.58/0.57    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.58/0.57    inference(superposition,[],[f74,f41])).
% 1.58/0.57  fof(f41,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (k10_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.58/0.57    inference(definition_unfolding,[],[f37,f31,f31])).
% 1.58/0.57  fof(f37,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f17])).
% 1.58/0.57  fof(f17,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.58/0.57    inference(flattening,[],[f16])).
% 1.58/0.57  fof(f16,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.58/0.57    inference(ennf_transformation,[],[f7])).
% 1.58/0.57  fof(f7,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).
% 1.58/0.57  fof(f74,plain,(
% 1.58/0.57    k10_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f26,f40])).
% 1.58/0.57  fof(f40,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.58/0.57    inference(definition_unfolding,[],[f32,f31])).
% 1.58/0.57  fof(f32,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f13])).
% 1.58/0.57  fof(f13,plain,(
% 1.58/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.58/0.57    inference(ennf_transformation,[],[f4])).
% 1.58/0.57  fof(f4,axiom,(
% 1.58/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.58/0.57  fof(f26,plain,(
% 1.58/0.57    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.58/0.57    inference(cnf_transformation,[],[f21])).
% 1.58/0.57  fof(f70,plain,(
% 1.58/0.57    ( ! [X0] : (~r1_tarski(sK0,k1_setfam_1(k2_tarski(X0,sK1)))) )),
% 1.58/0.57    inference(unit_resulting_resolution,[],[f44,f28,f38])).
% 1.58/0.57  fof(f28,plain,(
% 1.58/0.57    ~r1_tarski(sK0,sK1)),
% 1.58/0.57    inference(cnf_transformation,[],[f21])).
% 1.58/0.57  fof(f44,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 1.58/0.57    inference(superposition,[],[f39,f30])).
% 1.58/0.57  fof(f30,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f5])).
% 1.58/0.57  fof(f5,axiom,(
% 1.58/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.58/0.57  % SZS output end Proof for theBenchmark
% 1.58/0.57  % (7236)------------------------------
% 1.58/0.57  % (7236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (7236)Termination reason: Refutation
% 1.58/0.57  
% 1.58/0.57  % (7236)Memory used [KB]: 2302
% 1.58/0.57  % (7236)Time elapsed: 0.134 s
% 1.58/0.57  % (7236)------------------------------
% 1.58/0.57  % (7236)------------------------------
% 1.58/0.57  % (7261)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.58/0.57  % (7232)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.58/0.57  % (7251)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.58/0.58  % (7231)Success in time 0.212 s
%------------------------------------------------------------------------------
