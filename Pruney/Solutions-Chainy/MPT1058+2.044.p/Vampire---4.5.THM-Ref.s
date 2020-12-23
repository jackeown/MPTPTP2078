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
% DateTime   : Thu Dec  3 13:07:23 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   52 (  82 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 219 expanded)
%              Number of equality atoms :   40 (  72 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1326,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1325,f36])).

fof(f36,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f1325,plain,(
    ~ r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(trivial_inequality_removal,[],[f1303])).

fof(f1303,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2)
    | ~ r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(superposition,[],[f94,f200])).

fof(f200,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X5,X4) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(forward_demodulation,[],[f199,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f199,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X5,X4) = X4
      | ~ r1_tarski(k1_relat_1(k6_relat_1(X4)),X5) ) ),
    inference(subsumption_resolution,[],[f191,f38])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f191,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X5,X4) = X4
      | ~ v1_relat_1(k6_relat_1(X4))
      | ~ r1_tarski(k1_relat_1(k6_relat_1(X4)),X5) ) ),
    inference(superposition,[],[f91,f176])).

fof(f176,plain,(
    ! [X1] : k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1)) = X1 ),
    inference(subsumption_resolution,[],[f175,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f175,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,X1)
      | k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1)) = X1 ) ),
    inference(forward_demodulation,[],[f174,f39])).

fof(f174,plain,(
    ! [X1] :
      ( k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(k6_relat_1(X1))) ) ),
    inference(subsumption_resolution,[],[f168,f38])).

fof(f168,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f80,f57])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f56,f38])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f44,f39])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f47,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f52,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f94,plain,(
    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f90,f35])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f37,f52])).

fof(f37,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:43:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (29089)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (29088)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (29103)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (29095)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (29101)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (29093)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (29090)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (29099)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (29087)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (29109)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (29098)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (29111)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (29108)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (29086)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (29100)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (29115)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (29106)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (29091)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (29113)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (29112)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (29092)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (29110)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (29107)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (29105)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (29104)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (29102)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (29097)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (29094)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (29114)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (29096)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.64/0.63  % (29095)Refutation found. Thanks to Tanya!
% 1.64/0.63  % SZS status Theorem for theBenchmark
% 2.08/0.63  % SZS output start Proof for theBenchmark
% 2.08/0.63  fof(f1326,plain,(
% 2.08/0.63    $false),
% 2.08/0.63    inference(subsumption_resolution,[],[f1325,f36])).
% 2.08/0.63  fof(f36,plain,(
% 2.08/0.63    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.08/0.63    inference(cnf_transformation,[],[f32])).
% 2.08/0.63  fof(f32,plain,(
% 2.08/0.63    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_relat_1(sK0)),
% 2.08/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f31,f30])).
% 2.08/0.63  fof(f30,plain,(
% 2.08/0.63    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_relat_1(sK0))),
% 2.08/0.63    introduced(choice_axiom,[])).
% 2.08/0.63  fof(f31,plain,(
% 2.08/0.63    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 2.08/0.63    introduced(choice_axiom,[])).
% 2.08/0.63  fof(f18,plain,(
% 2.08/0.63    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0))),
% 2.08/0.63    inference(ennf_transformation,[],[f16])).
% 2.08/0.63  fof(f16,plain,(
% 2.08/0.63    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.08/0.63    inference(pure_predicate_removal,[],[f15])).
% 2.08/0.63  fof(f15,negated_conjecture,(
% 2.08/0.63    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.08/0.63    inference(negated_conjecture,[],[f14])).
% 2.08/0.63  fof(f14,conjecture,(
% 2.08/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.08/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 2.08/0.63  fof(f1325,plain,(
% 2.08/0.63    ~r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.08/0.63    inference(trivial_inequality_removal,[],[f1303])).
% 2.08/0.63  fof(f1303,plain,(
% 2.08/0.63    k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) | ~r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.08/0.63    inference(superposition,[],[f94,f200])).
% 2.08/0.63  fof(f200,plain,(
% 2.08/0.63    ( ! [X4,X5] : (k3_xboole_0(X5,X4) = X4 | ~r1_tarski(X4,X5)) )),
% 2.08/0.63    inference(forward_demodulation,[],[f199,f39])).
% 2.08/0.63  fof(f39,plain,(
% 2.08/0.63    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.08/0.63    inference(cnf_transformation,[],[f8])).
% 2.08/0.63  fof(f8,axiom,(
% 2.08/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.08/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.08/0.63  fof(f199,plain,(
% 2.08/0.63    ( ! [X4,X5] : (k3_xboole_0(X5,X4) = X4 | ~r1_tarski(k1_relat_1(k6_relat_1(X4)),X5)) )),
% 2.08/0.63    inference(subsumption_resolution,[],[f191,f38])).
% 2.08/0.63  fof(f38,plain,(
% 2.08/0.63    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.08/0.63    inference(cnf_transformation,[],[f17])).
% 2.08/0.63  fof(f17,plain,(
% 2.08/0.63    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.08/0.63    inference(pure_predicate_removal,[],[f11])).
% 2.08/0.63  fof(f11,axiom,(
% 2.08/0.63    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.08/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.08/0.63  fof(f191,plain,(
% 2.08/0.63    ( ! [X4,X5] : (k3_xboole_0(X5,X4) = X4 | ~v1_relat_1(k6_relat_1(X4)) | ~r1_tarski(k1_relat_1(k6_relat_1(X4)),X5)) )),
% 2.08/0.63    inference(superposition,[],[f91,f176])).
% 2.08/0.63  fof(f176,plain,(
% 2.08/0.63    ( ! [X1] : (k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1)) = X1) )),
% 2.08/0.63    inference(subsumption_resolution,[],[f175,f54])).
% 2.08/0.63  fof(f54,plain,(
% 2.08/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.08/0.63    inference(equality_resolution,[],[f50])).
% 2.08/0.63  fof(f50,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.08/0.63    inference(cnf_transformation,[],[f34])).
% 2.08/0.63  fof(f34,plain,(
% 2.08/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.63    inference(flattening,[],[f33])).
% 2.08/0.63  fof(f33,plain,(
% 2.08/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.63    inference(nnf_transformation,[],[f1])).
% 2.08/0.63  fof(f1,axiom,(
% 2.08/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.08/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.08/0.63  fof(f175,plain,(
% 2.08/0.63    ( ! [X1] : (~r1_tarski(X1,X1) | k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1)) = X1) )),
% 2.08/0.63    inference(forward_demodulation,[],[f174,f39])).
% 2.08/0.63  fof(f174,plain,(
% 2.08/0.63    ( ! [X1] : (k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1)) = X1 | ~r1_tarski(X1,k1_relat_1(k6_relat_1(X1)))) )),
% 2.08/0.63    inference(subsumption_resolution,[],[f168,f38])).
% 2.08/0.63  fof(f168,plain,(
% 2.08/0.63    ( ! [X1] : (~v1_relat_1(k6_relat_1(X1)) | k10_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X1)) = X1 | ~r1_tarski(X1,k1_relat_1(k6_relat_1(X1)))) )),
% 2.08/0.63    inference(resolution,[],[f80,f57])).
% 2.08/0.63  fof(f57,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.08/0.63    inference(subsumption_resolution,[],[f56,f38])).
% 2.08/0.63  fof(f56,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.08/0.63    inference(superposition,[],[f44,f39])).
% 2.08/0.63  fof(f44,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f20])).
% 2.08/0.63  fof(f20,plain,(
% 2.08/0.63    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.08/0.63    inference(ennf_transformation,[],[f7])).
% 2.08/0.63  fof(f7,axiom,(
% 2.08/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.08/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.08/0.63  fof(f80,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_relat_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) )),
% 2.08/0.63    inference(resolution,[],[f47,f51])).
% 2.08/0.63  fof(f51,plain,(
% 2.08/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f34])).
% 2.08/0.63  fof(f47,plain,(
% 2.08/0.63    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f24])).
% 2.08/0.63  fof(f24,plain,(
% 2.08/0.63    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.08/0.63    inference(flattening,[],[f23])).
% 2.08/0.63  fof(f23,plain,(
% 2.08/0.63    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.08/0.63    inference(ennf_transformation,[],[f13])).
% 2.08/0.63  fof(f13,axiom,(
% 2.08/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.08/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 2.08/0.63  fof(f91,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1)) )),
% 2.08/0.63    inference(duplicate_literal_removal,[],[f87])).
% 2.08/0.63  fof(f87,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 2.08/0.63    inference(superposition,[],[f52,f48])).
% 2.08/0.63  fof(f48,plain,(
% 2.08/0.63    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f26])).
% 2.08/0.63  fof(f26,plain,(
% 2.08/0.63    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.08/0.63    inference(flattening,[],[f25])).
% 2.08/0.63  fof(f25,plain,(
% 2.08/0.63    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.08/0.63    inference(ennf_transformation,[],[f10])).
% 2.08/0.63  fof(f10,axiom,(
% 2.08/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.08/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 2.08/0.63  fof(f52,plain,(
% 2.08/0.63    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.08/0.63    inference(cnf_transformation,[],[f27])).
% 2.08/0.63  fof(f27,plain,(
% 2.08/0.63    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.08/0.63    inference(ennf_transformation,[],[f12])).
% 2.08/0.63  fof(f12,axiom,(
% 2.08/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.08/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 2.08/0.63  fof(f94,plain,(
% 2.08/0.63    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 2.08/0.63    inference(subsumption_resolution,[],[f90,f35])).
% 2.08/0.63  fof(f35,plain,(
% 2.08/0.63    v1_relat_1(sK0)),
% 2.08/0.63    inference(cnf_transformation,[],[f32])).
% 2.08/0.63  fof(f90,plain,(
% 2.08/0.63    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0)),
% 2.08/0.63    inference(superposition,[],[f37,f52])).
% 2.08/0.63  fof(f37,plain,(
% 2.08/0.63    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.08/0.63    inference(cnf_transformation,[],[f32])).
% 2.08/0.63  % SZS output end Proof for theBenchmark
% 2.08/0.63  % (29095)------------------------------
% 2.08/0.63  % (29095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.63  % (29095)Termination reason: Refutation
% 2.08/0.63  
% 2.08/0.63  % (29095)Memory used [KB]: 2558
% 2.08/0.63  % (29095)Time elapsed: 0.204 s
% 2.08/0.63  % (29095)------------------------------
% 2.08/0.63  % (29095)------------------------------
% 2.08/0.64  % (29084)Success in time 0.274 s
%------------------------------------------------------------------------------
