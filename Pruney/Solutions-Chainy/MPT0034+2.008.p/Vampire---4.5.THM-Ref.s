%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:43 EST 2020

% Result     : Theorem 3.61s
% Output     : Refutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 122 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 310 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5451,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5277,f5439])).

fof(f5439,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(superposition,[],[f228,f3192])).

fof(f3192,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),X1) = X1 ),
    inference(unit_resulting_resolution,[],[f139,f761])).

fof(f761,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k3_xboole_0(X2,X3) = X3 ) ),
    inference(global_subsumption,[],[f210,f758])).

fof(f758,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f756])).

fof(f756,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2)
      | k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f43,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK4(X0,X1,X2),X0)
        & r1_tarski(sK4(X0,X1,X2),X2)
        & r1_tarski(sK4(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK4(X0,X1,X2),X0)
        & r1_tarski(sK4(X0,X1,X2),X2)
        & r1_tarski(sK4(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK4(X0,X1,X2),X0)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f210,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f139,f46])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f32,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f139,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f127,f46])).

fof(f127,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f32,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f228,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X2),X1)) ),
    inference(unit_resulting_resolution,[],[f33,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f5277,plain,(
    ! [X0] : ~ r1_tarski(k3_xboole_0(k2_xboole_0(sK1,X0),sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f1205,f228,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1205,plain,(
    ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f576,f235,f39])).

fof(f235,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f29,f37])).

fof(f29,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

fof(f576,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f30,f448,f39])).

fof(f448,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f74,f31,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f31,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f29,f34,f39])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f30,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:06:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (22870)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (22878)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (22865)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (22866)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (22868)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (22869)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (22867)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (22881)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (22871)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (22876)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (22873)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (22887)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (22883)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (22877)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (22886)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.52  % (22888)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.52  % (22880)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (22885)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (22884)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.52  % (22875)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.53  % (22882)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.53  % (22872)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.53  % (22879)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.33/0.53  % (22874)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 3.61/0.84  % (22879)Refutation found. Thanks to Tanya!
% 3.61/0.84  % SZS status Theorem for theBenchmark
% 3.61/0.84  % SZS output start Proof for theBenchmark
% 3.61/0.84  fof(f5451,plain,(
% 3.61/0.84    $false),
% 3.61/0.84    inference(subsumption_resolution,[],[f5277,f5439])).
% 3.61/0.84  fof(f5439,plain,(
% 3.61/0.84    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X1,X2),X2)) )),
% 3.61/0.84    inference(superposition,[],[f228,f3192])).
% 3.61/0.84  fof(f3192,plain,(
% 3.61/0.84    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X0,X1),X1) = X1) )),
% 3.61/0.84    inference(unit_resulting_resolution,[],[f139,f761])).
% 3.61/0.84  fof(f761,plain,(
% 3.61/0.84    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k3_xboole_0(X2,X3) = X3) )),
% 3.61/0.84    inference(global_subsumption,[],[f210,f758])).
% 3.61/0.84  fof(f758,plain,(
% 3.61/0.84    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2)) )),
% 3.61/0.84    inference(duplicate_literal_removal,[],[f756])).
% 3.61/0.84  fof(f756,plain,(
% 3.61/0.84    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2) | k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2)) )),
% 3.61/0.84    inference(resolution,[],[f43,f42])).
% 3.61/0.84  fof(f42,plain,(
% 3.61/0.84    ( ! [X2,X0,X1] : (r1_tarski(sK4(X0,X1,X2),X2) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f28])).
% 3.61/0.84  fof(f28,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK4(X0,X1,X2),X0) & r1_tarski(sK4(X0,X1,X2),X2) & r1_tarski(sK4(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.61/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f27])).
% 3.61/0.84  fof(f27,plain,(
% 3.61/0.84    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK4(X0,X1,X2),X0) & r1_tarski(sK4(X0,X1,X2),X2) & r1_tarski(sK4(X0,X1,X2),X1)))),
% 3.61/0.84    introduced(choice_axiom,[])).
% 3.61/0.84  fof(f24,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.61/0.84    inference(flattening,[],[f23])).
% 3.61/0.84  fof(f23,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.61/0.84    inference(ennf_transformation,[],[f6])).
% 3.61/0.84  fof(f6,axiom,(
% 3.61/0.84    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 3.61/0.84  fof(f43,plain,(
% 3.61/0.84    ( ! [X2,X0,X1] : (~r1_tarski(sK4(X0,X1,X2),X0) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f28])).
% 3.61/0.84  fof(f210,plain,(
% 3.61/0.84    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.61/0.84    inference(superposition,[],[f139,f46])).
% 3.61/0.84  fof(f46,plain,(
% 3.61/0.84    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 3.61/0.84    inference(unit_resulting_resolution,[],[f32,f35])).
% 3.61/0.84  fof(f35,plain,(
% 3.61/0.84    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.61/0.84    inference(cnf_transformation,[],[f15])).
% 3.61/0.84  fof(f15,plain,(
% 3.61/0.84    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.61/0.84    inference(ennf_transformation,[],[f2])).
% 3.61/0.84  fof(f2,axiom,(
% 3.61/0.84    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.61/0.84  fof(f32,plain,(
% 3.61/0.84    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f8])).
% 3.61/0.84  fof(f8,axiom,(
% 3.61/0.84    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.61/0.84  fof(f139,plain,(
% 3.61/0.84    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 3.61/0.84    inference(forward_demodulation,[],[f127,f46])).
% 3.61/0.84  fof(f127,plain,(
% 3.61/0.84    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X1,X0))) )),
% 3.61/0.84    inference(unit_resulting_resolution,[],[f32,f36])).
% 3.61/0.84  fof(f36,plain,(
% 3.61/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 3.61/0.84    inference(cnf_transformation,[],[f16])).
% 3.61/0.84  fof(f16,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 3.61/0.84    inference(ennf_transformation,[],[f10])).
% 3.61/0.84  fof(f10,axiom,(
% 3.61/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
% 3.61/0.84  fof(f228,plain,(
% 3.61/0.84    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X2),X1))) )),
% 3.61/0.84    inference(unit_resulting_resolution,[],[f33,f37])).
% 3.61/0.84  fof(f37,plain,(
% 3.61/0.84    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f17])).
% 3.61/0.84  fof(f17,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 3.61/0.84    inference(ennf_transformation,[],[f7])).
% 3.61/0.84  fof(f7,axiom,(
% 3.61/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).
% 3.61/0.84  fof(f33,plain,(
% 3.61/0.84    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.61/0.84    inference(cnf_transformation,[],[f9])).
% 3.61/0.84  fof(f9,axiom,(
% 3.61/0.84    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.61/0.84  fof(f5277,plain,(
% 3.61/0.84    ( ! [X0] : (~r1_tarski(k3_xboole_0(k2_xboole_0(sK1,X0),sK2),sK2)) )),
% 3.61/0.84    inference(unit_resulting_resolution,[],[f1205,f228,f39])).
% 3.61/0.84  fof(f39,plain,(
% 3.61/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f20])).
% 3.61/0.84  fof(f20,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.61/0.84    inference(flattening,[],[f19])).
% 3.61/0.84  fof(f19,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.61/0.84    inference(ennf_transformation,[],[f5])).
% 3.61/0.84  fof(f5,axiom,(
% 3.61/0.84    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.61/0.84  fof(f1205,plain,(
% 3.61/0.84    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2)),
% 3.61/0.84    inference(unit_resulting_resolution,[],[f576,f235,f39])).
% 3.61/0.84  fof(f235,plain,(
% 3.61/0.84    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,X0))) )),
% 3.61/0.84    inference(unit_resulting_resolution,[],[f29,f37])).
% 3.61/0.84  fof(f29,plain,(
% 3.61/0.84    r1_tarski(sK0,sK1)),
% 3.61/0.84    inference(cnf_transformation,[],[f26])).
% 3.61/0.84  fof(f26,plain,(
% 3.61/0.84    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 3.61/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).
% 3.61/0.84  fof(f25,plain,(
% 3.61/0.84    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 3.61/0.84    introduced(choice_axiom,[])).
% 3.61/0.84  fof(f14,plain,(
% 3.61/0.84    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 3.61/0.84    inference(flattening,[],[f13])).
% 3.61/0.84  fof(f13,plain,(
% 3.61/0.84    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 3.61/0.84    inference(ennf_transformation,[],[f12])).
% 3.61/0.84  fof(f12,negated_conjecture,(
% 3.61/0.84    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 3.61/0.84    inference(negated_conjecture,[],[f11])).
% 3.61/0.84  fof(f11,conjecture,(
% 3.61/0.84    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).
% 3.61/0.84  fof(f576,plain,(
% 3.61/0.84    ~r1_tarski(k3_xboole_0(sK0,sK2),sK2)),
% 3.61/0.84    inference(unit_resulting_resolution,[],[f30,f448,f39])).
% 3.61/0.84  fof(f448,plain,(
% 3.61/0.84    ~r1_tarski(k3_xboole_0(sK0,sK2),sK3)),
% 3.61/0.84    inference(unit_resulting_resolution,[],[f74,f31,f40])).
% 3.61/0.84  fof(f40,plain,(
% 3.61/0.84    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f22])).
% 3.61/0.84  fof(f22,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.61/0.84    inference(flattening,[],[f21])).
% 3.61/0.84  fof(f21,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.61/0.84    inference(ennf_transformation,[],[f4])).
% 3.61/0.84  fof(f4,axiom,(
% 3.61/0.84    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 3.61/0.84  fof(f31,plain,(
% 3.61/0.84    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 3.61/0.84    inference(cnf_transformation,[],[f26])).
% 3.61/0.84  fof(f74,plain,(
% 3.61/0.84    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),sK1)) )),
% 3.61/0.84    inference(unit_resulting_resolution,[],[f29,f34,f39])).
% 3.61/0.84  fof(f34,plain,(
% 3.61/0.84    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f3])).
% 3.61/0.84  fof(f3,axiom,(
% 3.61/0.84    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.61/0.84  fof(f30,plain,(
% 3.61/0.84    r1_tarski(sK2,sK3)),
% 3.61/0.84    inference(cnf_transformation,[],[f26])).
% 3.61/0.84  % SZS output end Proof for theBenchmark
% 3.61/0.84  % (22879)------------------------------
% 3.61/0.84  % (22879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.84  % (22879)Termination reason: Refutation
% 3.61/0.84  
% 3.61/0.84  % (22879)Memory used [KB]: 14967
% 3.61/0.84  % (22879)Time elapsed: 0.390 s
% 3.61/0.84  % (22879)------------------------------
% 3.61/0.84  % (22879)------------------------------
% 3.61/0.84  % (22864)Success in time 0.478 s
%------------------------------------------------------------------------------
