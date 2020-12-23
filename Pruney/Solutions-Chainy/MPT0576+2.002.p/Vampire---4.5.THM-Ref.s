%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:46 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  74 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 320 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(subsumption_resolution,[],[f358,f169])).

fof(f169,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2)) ),
    inference(subsumption_resolution,[],[f63,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t180_relat_1)).

fof(f63,plain,(
    ! [X2] :
      ( r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f52,f26])).

fof(f26,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X2] :
      ( r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2))
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

fof(f27,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_relat_1(sK3,sK1))
      | ~ r1_tarski(k10_relat_1(sK2,sK0),X0) ) ),
    inference(resolution,[],[f29,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f29,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f358,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f247,f65])).

fof(f65,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f247,plain,(
    ! [X2,X3] : r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f38,f43])).

fof(f43,plain,(
    ! [X4,X5] : k10_relat_1(sK2,k2_xboole_0(X4,X5)) = k2_xboole_0(k10_relat_1(sK2,X4),k10_relat_1(sK2,X5)) ),
    inference(resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:27:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (805502976)
% 0.14/0.39  ipcrm: permission denied for id (805535755)
% 0.14/0.41  ipcrm: permission denied for id (805634077)
% 0.23/0.48  ipcrm: permission denied for id (805732439)
% 0.23/0.49  ipcrm: permission denied for id (805765212)
% 0.23/0.51  ipcrm: permission denied for id (805797990)
% 0.85/0.66  % (15038)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.85/0.67  % (15044)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.85/0.67  % (15046)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.85/0.67  % (15033)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.21/0.68  % (15036)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.21/0.68  % (15041)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.21/0.68  % (15036)Refutation found. Thanks to Tanya!
% 1.21/0.68  % SZS status Theorem for theBenchmark
% 1.21/0.69  % (15027)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.21/0.69  % (15050)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.21/0.69  % (15031)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.21/0.69  % (15025)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.21/0.70  % (15035)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.21/0.70  % (15047)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.21/0.70  % (15045)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.21/0.70  % (15048)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.21/0.70  % (15040)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.21/0.70  % (15039)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.21/0.71  % (15042)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.21/0.71  % (15029)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.21/0.71  % (15032)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.21/0.71  % SZS output start Proof for theBenchmark
% 1.21/0.71  fof(f360,plain,(
% 1.21/0.71    $false),
% 1.21/0.71    inference(subsumption_resolution,[],[f358,f169])).
% 1.21/0.71  fof(f169,plain,(
% 1.21/0.71    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.21/0.71    inference(resolution,[],[f94,f64])).
% 1.21/0.71  fof(f64,plain,(
% 1.21/0.71    ( ! [X2] : (r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2))) )),
% 1.21/0.71    inference(subsumption_resolution,[],[f63,f25])).
% 1.21/0.71  fof(f25,plain,(
% 1.21/0.71    v1_relat_1(sK2)),
% 1.21/0.71    inference(cnf_transformation,[],[f22])).
% 1.21/0.71  fof(f22,plain,(
% 1.21/0.71    (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.21/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f21,f20])).
% 1.21/0.71  fof(f20,plain,(
% 1.21/0.71    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 1.21/0.71    introduced(choice_axiom,[])).
% 1.21/0.71  fof(f21,plain,(
% 1.21/0.71    ? [X3] : (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 1.21/0.71    introduced(choice_axiom,[])).
% 1.21/0.71  fof(f13,plain,(
% 1.21/0.71    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.21/0.71    inference(flattening,[],[f12])).
% 1.21/0.71  fof(f12,plain,(
% 1.21/0.71    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.21/0.71    inference(ennf_transformation,[],[f11])).
% 1.21/0.71  fof(f11,negated_conjecture,(
% 1.21/0.71    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)))))),
% 1.21/0.71    inference(negated_conjecture,[],[f10])).
% 1.21/0.71  fof(f10,conjecture,(
% 1.21/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)))))),
% 1.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t180_relat_1)).
% 1.21/0.71  fof(f63,plain,(
% 1.21/0.71    ( ! [X2] : (r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2)) | ~v1_relat_1(sK2)) )),
% 1.21/0.71    inference(subsumption_resolution,[],[f52,f26])).
% 1.21/0.71  fof(f26,plain,(
% 1.21/0.71    v1_relat_1(sK3)),
% 1.21/0.71    inference(cnf_transformation,[],[f22])).
% 1.21/0.71  fof(f52,plain,(
% 1.21/0.71    ( ! [X2] : (r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2)) )),
% 1.21/0.71    inference(resolution,[],[f27,f31])).
% 1.21/0.71  fof(f31,plain,(
% 1.21/0.71    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.21/0.71    inference(cnf_transformation,[],[f16])).
% 1.21/0.71  fof(f16,plain,(
% 1.21/0.71    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.21/0.71    inference(flattening,[],[f15])).
% 1.21/0.71  fof(f15,plain,(
% 1.21/0.71    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.21/0.71    inference(ennf_transformation,[],[f9])).
% 1.21/0.71  fof(f9,axiom,(
% 1.21/0.71    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 1.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).
% 1.21/0.71  fof(f27,plain,(
% 1.21/0.71    r1_tarski(sK2,sK3)),
% 1.21/0.71    inference(cnf_transformation,[],[f22])).
% 1.21/0.71  fof(f94,plain,(
% 1.21/0.71    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK3,sK1)) | ~r1_tarski(k10_relat_1(sK2,sK0),X0)) )),
% 1.21/0.71    inference(resolution,[],[f29,f32])).
% 1.21/0.71  fof(f32,plain,(
% 1.21/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.21/0.71    inference(cnf_transformation,[],[f18])).
% 1.21/0.71  fof(f18,plain,(
% 1.21/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.21/0.71    inference(flattening,[],[f17])).
% 1.21/0.71  fof(f17,plain,(
% 1.21/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.21/0.71    inference(ennf_transformation,[],[f4])).
% 1.21/0.71  fof(f4,axiom,(
% 1.21/0.71    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.21/0.71  fof(f29,plain,(
% 1.21/0.71    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))),
% 1.21/0.71    inference(cnf_transformation,[],[f22])).
% 1.21/0.71  fof(f358,plain,(
% 1.21/0.71    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.21/0.71    inference(superposition,[],[f247,f65])).
% 1.21/0.71  fof(f65,plain,(
% 1.21/0.71    sK1 = k2_xboole_0(sK0,sK1)),
% 1.21/0.71    inference(resolution,[],[f28,f36])).
% 1.21/0.71  fof(f36,plain,(
% 1.21/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.21/0.71    inference(cnf_transformation,[],[f19])).
% 1.21/0.71  fof(f19,plain,(
% 1.21/0.71    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.21/0.71    inference(ennf_transformation,[],[f3])).
% 1.21/0.71  fof(f3,axiom,(
% 1.21/0.71    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.21/0.71  fof(f28,plain,(
% 1.21/0.71    r1_tarski(sK0,sK1)),
% 1.21/0.71    inference(cnf_transformation,[],[f22])).
% 1.21/0.71  fof(f247,plain,(
% 1.21/0.71    ( ! [X2,X3] : (r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k2_xboole_0(X2,X3)))) )),
% 1.21/0.71    inference(superposition,[],[f38,f43])).
% 1.21/0.71  fof(f43,plain,(
% 1.21/0.71    ( ! [X4,X5] : (k10_relat_1(sK2,k2_xboole_0(X4,X5)) = k2_xboole_0(k10_relat_1(sK2,X4),k10_relat_1(sK2,X5))) )),
% 1.21/0.71    inference(resolution,[],[f25,f30])).
% 1.21/0.71  fof(f30,plain,(
% 1.21/0.71    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.21/0.71    inference(cnf_transformation,[],[f14])).
% 1.21/0.71  fof(f14,plain,(
% 1.21/0.71    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.21/0.71    inference(ennf_transformation,[],[f8])).
% 1.21/0.71  fof(f8,axiom,(
% 1.21/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 1.21/0.71  fof(f38,plain,(
% 1.21/0.71    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.21/0.71    inference(cnf_transformation,[],[f7])).
% 1.21/0.71  fof(f7,axiom,(
% 1.21/0.71    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.21/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.21/0.71  % SZS output end Proof for theBenchmark
% 1.21/0.71  % (15036)------------------------------
% 1.21/0.71  % (15036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.71  % (15036)Termination reason: Refutation
% 1.21/0.71  
% 1.21/0.71  % (15036)Memory used [KB]: 10874
% 1.21/0.71  % (15036)Time elapsed: 0.075 s
% 1.21/0.71  % (15036)------------------------------
% 1.21/0.71  % (15036)------------------------------
% 1.21/0.71  % (14860)Success in time 0.343 s
%------------------------------------------------------------------------------
