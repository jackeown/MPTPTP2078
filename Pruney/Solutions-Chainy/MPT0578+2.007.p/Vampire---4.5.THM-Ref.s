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
% DateTime   : Thu Dec  3 12:50:48 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   59 (  97 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   17
%              Number of atoms          :  159 ( 281 expanded)
%              Number of equality atoms :   35 (  74 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f746,plain,(
    $false ),
    inference(subsumption_resolution,[],[f745,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f745,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f744,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f744,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f698])).

fof(f698,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f26,f696])).

fof(f696,plain,(
    ! [X2,X3] :
      ( k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(X2,k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f693,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f56,f27])).

fof(f27,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f56,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k10_relat_1(X3,k10_relat_1(X4,X5)),k1_relat_1(k5_relat_1(X3,X4)))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f52,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f52,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k10_relat_1(X3,k10_relat_1(X4,X5)),k1_relat_1(k5_relat_1(X3,X4)))
      | ~ v1_relat_1(k5_relat_1(X3,X4))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f29,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f693,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(X2,k1_relat_1(X3))
      | ~ r1_tarski(k10_relat_1(X2,k1_relat_1(X3)),k1_relat_1(k5_relat_1(X2,X3))) ) ),
    inference(resolution,[],[f681,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f681,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k10_relat_1(X0,k1_relat_1(X1)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f678])).

fof(f678,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k10_relat_1(X0,k1_relat_1(X1)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f306,f54])).

fof(f54,plain,(
    ! [X4,X3] :
      ( k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4))))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f50,f31])).

fof(f50,plain,(
    ! [X4,X3] :
      ( k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4))))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f30,f27])).

fof(f306,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k10_relat_1(X8,k10_relat_1(X6,X7)),k10_relat_1(X8,k1_relat_1(X6)))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f65,f212])).

fof(f212,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f201,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f190,f43])).

fof(f43,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k2_xboole_0(X3,X4),X5)
      | k2_xboole_0(X3,X4) = X5
      | ~ r1_tarski(X5,X4) ) ),
    inference(resolution,[],[f34,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f190,plain,(
    ! [X12,X11] :
      ( r1_tarski(k2_xboole_0(k10_relat_1(X11,X12),k1_relat_1(X11)),k1_relat_1(X11))
      | ~ v1_relat_1(X11) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X12,X11] :
      ( r1_tarski(k2_xboole_0(k10_relat_1(X11,X12),k1_relat_1(X11)),k1_relat_1(X11))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X11) ) ),
    inference(superposition,[],[f29,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k2_xboole_0(X1,k2_relat_1(X0))) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k2_xboole_0(X1,k2_relat_1(X0))) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f35,f27])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

% (8014)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (8017)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f65,plain,(
    ! [X12,X13,X11] :
      ( r1_tarski(k10_relat_1(X11,X12),k10_relat_1(X11,k2_xboole_0(X12,X13)))
      | ~ v1_relat_1(X11) ) ),
    inference(superposition,[],[f28,f35])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f26,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.31/0.53  % (7996)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.53  % (8000)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.31/0.54  % (8010)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.31/0.54  % (7995)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.49/0.55  % (8012)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.49/0.55  % (8021)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.49/0.55  % (8005)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.49/0.56  % (7999)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.49/0.56  % (8008)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.49/0.57  % (8011)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.49/0.57  % (7998)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.49/0.57  % (8007)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.49/0.57  % (8004)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.49/0.57  % (8001)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.49/0.57  % (8003)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.49/0.58  % (8019)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.49/0.58  % (8013)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.49/0.58  % (8015)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.49/0.58  % (8020)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.49/0.58  % (8002)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.49/0.58  % (8000)Refutation found. Thanks to Tanya!
% 1.49/0.58  % SZS status Theorem for theBenchmark
% 1.49/0.58  % SZS output start Proof for theBenchmark
% 1.49/0.58  fof(f746,plain,(
% 1.49/0.58    $false),
% 1.49/0.58    inference(subsumption_resolution,[],[f745,f24])).
% 1.49/0.59  fof(f24,plain,(
% 1.49/0.59    v1_relat_1(sK0)),
% 1.49/0.59    inference(cnf_transformation,[],[f21])).
% 1.49/0.59  fof(f21,plain,(
% 1.49/0.59    (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.49/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20,f19])).
% 1.49/0.59  fof(f19,plain,(
% 1.49/0.59    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.49/0.59  fof(f20,plain,(
% 1.49/0.59    ? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.49/0.59  fof(f11,plain,(
% 1.49/0.59    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f10])).
% 1.49/0.59  fof(f10,negated_conjecture,(
% 1.49/0.59    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.49/0.59    inference(negated_conjecture,[],[f9])).
% 1.49/0.59  fof(f9,conjecture,(
% 1.49/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.49/0.59  fof(f745,plain,(
% 1.49/0.59    ~v1_relat_1(sK0)),
% 1.49/0.59    inference(subsumption_resolution,[],[f744,f25])).
% 1.49/0.59  fof(f25,plain,(
% 1.49/0.59    v1_relat_1(sK1)),
% 1.49/0.59    inference(cnf_transformation,[],[f21])).
% 1.49/0.59  fof(f744,plain,(
% 1.49/0.59    ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 1.49/0.59    inference(trivial_inequality_removal,[],[f698])).
% 1.49/0.59  fof(f698,plain,(
% 1.49/0.59    k10_relat_1(sK0,k1_relat_1(sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 1.49/0.59    inference(superposition,[],[f26,f696])).
% 1.49/0.59  fof(f696,plain,(
% 1.49/0.59    ( ! [X2,X3] : (k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(X2,k1_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f693,f132])).
% 1.49/0.59  fof(f132,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 1.49/0.59    inference(duplicate_literal_removal,[],[f125])).
% 1.49/0.59  fof(f125,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k1_relat_1(X0)),k1_relat_1(k5_relat_1(X1,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.59    inference(superposition,[],[f56,f27])).
% 1.49/0.59  fof(f27,plain,(
% 1.49/0.59    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f12])).
% 1.49/0.59  fof(f12,plain,(
% 1.49/0.59    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.59    inference(ennf_transformation,[],[f6])).
% 1.49/0.59  fof(f6,axiom,(
% 1.49/0.59    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.49/0.59  fof(f56,plain,(
% 1.49/0.59    ( ! [X4,X5,X3] : (r1_tarski(k10_relat_1(X3,k10_relat_1(X4,X5)),k1_relat_1(k5_relat_1(X3,X4))) | ~v1_relat_1(X4) | ~v1_relat_1(X3)) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f52,f31])).
% 1.49/0.59  fof(f31,plain,(
% 1.49/0.59    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f16])).
% 1.49/0.59  fof(f16,plain,(
% 1.49/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.49/0.59    inference(flattening,[],[f15])).
% 1.49/0.59  fof(f15,plain,(
% 1.49/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.49/0.59    inference(ennf_transformation,[],[f4])).
% 1.49/0.59  fof(f4,axiom,(
% 1.49/0.59    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.49/0.59  fof(f52,plain,(
% 1.49/0.59    ( ! [X4,X5,X3] : (r1_tarski(k10_relat_1(X3,k10_relat_1(X4,X5)),k1_relat_1(k5_relat_1(X3,X4))) | ~v1_relat_1(k5_relat_1(X3,X4)) | ~v1_relat_1(X4) | ~v1_relat_1(X3)) )),
% 1.49/0.59    inference(superposition,[],[f29,f30])).
% 1.49/0.59  fof(f30,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f14])).
% 1.49/0.59  fof(f14,plain,(
% 1.49/0.59    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f8])).
% 1.49/0.59  fof(f8,axiom,(
% 1.49/0.59    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 1.49/0.59  fof(f29,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f13])).
% 1.49/0.59  fof(f13,plain,(
% 1.49/0.59    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f5])).
% 1.49/0.59  fof(f5,axiom,(
% 1.49/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.49/0.59  fof(f693,plain,(
% 1.49/0.59    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k1_relat_1(k5_relat_1(X2,X3)) = k10_relat_1(X2,k1_relat_1(X3)) | ~r1_tarski(k10_relat_1(X2,k1_relat_1(X3)),k1_relat_1(k5_relat_1(X2,X3)))) )),
% 1.49/0.59    inference(resolution,[],[f681,f34])).
% 1.49/0.59  fof(f34,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f23,plain,(
% 1.49/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.59    inference(flattening,[],[f22])).
% 1.49/0.59  fof(f22,plain,(
% 1.49/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.59    inference(nnf_transformation,[],[f1])).
% 1.49/0.59  fof(f1,axiom,(
% 1.49/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.59  fof(f681,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k10_relat_1(X0,k1_relat_1(X1))) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 1.49/0.59    inference(duplicate_literal_removal,[],[f678])).
% 1.49/0.59  fof(f678,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k10_relat_1(X0,k1_relat_1(X1))) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.59    inference(superposition,[],[f306,f54])).
% 1.49/0.59  fof(f54,plain,(
% 1.49/0.59    ( ! [X4,X3] : (k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4)))) | ~v1_relat_1(X4) | ~v1_relat_1(X3)) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f50,f31])).
% 1.49/0.59  fof(f50,plain,(
% 1.49/0.59    ( ! [X4,X3] : (k1_relat_1(k5_relat_1(X3,X4)) = k10_relat_1(X3,k10_relat_1(X4,k2_relat_1(k5_relat_1(X3,X4)))) | ~v1_relat_1(X4) | ~v1_relat_1(X3) | ~v1_relat_1(k5_relat_1(X3,X4))) )),
% 1.49/0.59    inference(superposition,[],[f30,f27])).
% 1.49/0.59  fof(f306,plain,(
% 1.49/0.59    ( ! [X6,X8,X7] : (r1_tarski(k10_relat_1(X8,k10_relat_1(X6,X7)),k10_relat_1(X8,k1_relat_1(X6))) | ~v1_relat_1(X8) | ~v1_relat_1(X6)) )),
% 1.49/0.59    inference(superposition,[],[f65,f212])).
% 1.49/0.59  fof(f212,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k1_relat_1(X0) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.49/0.59    inference(subsumption_resolution,[],[f201,f37])).
% 1.49/0.59  fof(f37,plain,(
% 1.49/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.49/0.59    inference(equality_resolution,[],[f33])).
% 1.49/0.59  fof(f33,plain,(
% 1.49/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.49/0.59    inference(cnf_transformation,[],[f23])).
% 1.49/0.59  fof(f201,plain,(
% 1.49/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X0))) )),
% 1.49/0.59    inference(resolution,[],[f190,f43])).
% 1.49/0.59  fof(f43,plain,(
% 1.49/0.59    ( ! [X4,X5,X3] : (~r1_tarski(k2_xboole_0(X3,X4),X5) | k2_xboole_0(X3,X4) = X5 | ~r1_tarski(X5,X4)) )),
% 1.49/0.59    inference(resolution,[],[f34,f36])).
% 1.49/0.59  fof(f36,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f18])).
% 1.49/0.59  fof(f18,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.49/0.59    inference(ennf_transformation,[],[f2])).
% 1.49/0.59  fof(f2,axiom,(
% 1.49/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.49/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.49/0.59  fof(f190,plain,(
% 1.49/0.59    ( ! [X12,X11] : (r1_tarski(k2_xboole_0(k10_relat_1(X11,X12),k1_relat_1(X11)),k1_relat_1(X11)) | ~v1_relat_1(X11)) )),
% 1.49/0.59    inference(duplicate_literal_removal,[],[f176])).
% 1.49/0.59  fof(f176,plain,(
% 1.49/0.59    ( ! [X12,X11] : (r1_tarski(k2_xboole_0(k10_relat_1(X11,X12),k1_relat_1(X11)),k1_relat_1(X11)) | ~v1_relat_1(X11) | ~v1_relat_1(X11)) )),
% 1.49/0.59    inference(superposition,[],[f29,f66])).
% 1.49/0.59  fof(f66,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k10_relat_1(X0,k2_xboole_0(X1,k2_relat_1(X0))) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.49/0.59    inference(duplicate_literal_removal,[],[f60])).
% 1.49/0.59  fof(f60,plain,(
% 1.49/0.59    ( ! [X0,X1] : (k10_relat_1(X0,k2_xboole_0(X1,k2_relat_1(X0))) = k2_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.59    inference(superposition,[],[f35,f27])).
% 1.49/0.59  fof(f35,plain,(
% 1.49/0.59    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.49/0.59    inference(cnf_transformation,[],[f17])).
% 1.49/0.59  fof(f17,plain,(
% 1.49/0.59    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.49/0.59    inference(ennf_transformation,[],[f7])).
% 1.49/0.59  % (8014)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.49/0.59  % (8017)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.49/0.60  fof(f7,axiom,(
% 1.49/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 1.49/0.60  fof(f65,plain,(
% 1.49/0.60    ( ! [X12,X13,X11] : (r1_tarski(k10_relat_1(X11,X12),k10_relat_1(X11,k2_xboole_0(X12,X13))) | ~v1_relat_1(X11)) )),
% 1.49/0.60    inference(superposition,[],[f28,f35])).
% 1.49/0.60  fof(f28,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f3])).
% 1.49/0.60  fof(f3,axiom,(
% 1.49/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.49/0.60  fof(f26,plain,(
% 1.49/0.60    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))),
% 1.49/0.60    inference(cnf_transformation,[],[f21])).
% 1.49/0.60  % SZS output end Proof for theBenchmark
% 1.49/0.60  % (8000)------------------------------
% 1.49/0.60  % (8000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (8000)Termination reason: Refutation
% 1.49/0.60  
% 1.49/0.60  % (8000)Memory used [KB]: 6524
% 1.49/0.60  % (8000)Time elapsed: 0.150 s
% 1.49/0.60  % (8000)------------------------------
% 1.49/0.60  % (8000)------------------------------
% 1.49/0.61  % (7994)Success in time 0.246 s
%------------------------------------------------------------------------------
