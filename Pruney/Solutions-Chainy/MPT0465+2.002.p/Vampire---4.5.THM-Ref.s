%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:31 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   47 (  97 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 336 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f459,plain,(
    $false ),
    inference(subsumption_resolution,[],[f457,f71])).

fof(f71,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f70,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f70,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f69,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relat_1)).

fof(f69,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f68,f26])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f67,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k4_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f25,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ v1_relat_1(k4_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f53,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relat_1)).

fof(f53,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f40,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f40,plain,(
    ~ r1_tarski(k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f39,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f39,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f27,f33])).

fof(f27,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f457,plain,(
    r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(resolution,[],[f451,f38])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
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

fof(f451,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k5_relat_1(sK0,sK1))
      | r1_tarski(X0,k5_relat_1(sK0,k2_xboole_0(sK2,sK1))) ) ),
    inference(superposition,[],[f29,f241])).

fof(f241,plain,(
    k5_relat_1(sK0,k2_xboole_0(sK2,sK1)) = k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f82,f26])).

fof(f82,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | k5_relat_1(sK0,k2_xboole_0(X13,sK1)) = k2_xboole_0(k5_relat_1(sK0,X13),k5_relat_1(sK0,sK1)) ) ),
    inference(resolution,[],[f42,f25])).

fof(f42,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(sK0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f24,f34])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:24:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (23091)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (23116)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (23104)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (23099)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (23096)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (23093)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (23094)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (23110)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (23101)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (23111)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (23095)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (23089)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (23119)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (23119)Refutation not found, incomplete strategy% (23119)------------------------------
% 0.21/0.54  % (23119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23119)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23119)Memory used [KB]: 10618
% 0.21/0.54  % (23119)Time elapsed: 0.128 s
% 0.21/0.54  % (23119)------------------------------
% 0.21/0.54  % (23119)------------------------------
% 0.21/0.54  % (23100)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (23105)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (23117)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (23107)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (23097)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (23106)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (23102)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (23106)Refutation not found, incomplete strategy% (23106)------------------------------
% 0.21/0.55  % (23106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23115)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (23106)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23106)Memory used [KB]: 10618
% 0.21/0.55  % (23106)Time elapsed: 0.141 s
% 0.21/0.55  % (23106)------------------------------
% 0.21/0.55  % (23106)------------------------------
% 0.21/0.55  % (23112)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (23120)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (23120)Refutation not found, incomplete strategy% (23120)------------------------------
% 0.21/0.56  % (23120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (23120)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (23120)Memory used [KB]: 1663
% 0.21/0.56  % (23120)Time elapsed: 0.129 s
% 0.21/0.56  % (23120)------------------------------
% 0.21/0.56  % (23120)------------------------------
% 0.21/0.56  % (23103)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (23113)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (23108)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (23100)Refutation not found, incomplete strategy% (23100)------------------------------
% 0.21/0.57  % (23100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (23100)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (23100)Memory used [KB]: 10618
% 0.21/0.57  % (23100)Time elapsed: 0.145 s
% 0.21/0.57  % (23100)------------------------------
% 0.21/0.57  % (23100)------------------------------
% 0.21/0.57  % (23090)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.66/0.58  % (23118)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.66/0.59  % (23109)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.66/0.59  % (23102)Refutation found. Thanks to Tanya!
% 1.66/0.59  % SZS status Theorem for theBenchmark
% 1.66/0.60  % SZS output start Proof for theBenchmark
% 1.66/0.60  fof(f459,plain,(
% 1.66/0.60    $false),
% 1.66/0.60    inference(subsumption_resolution,[],[f457,f71])).
% 1.66/0.60  fof(f71,plain,(
% 1.66/0.60    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1)))),
% 1.66/0.60    inference(forward_demodulation,[],[f70,f36])).
% 1.66/0.60  fof(f36,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f3])).
% 1.66/0.60  fof(f3,axiom,(
% 1.66/0.60    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.66/0.60  fof(f70,plain,(
% 1.66/0.60    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))),
% 1.66/0.60    inference(subsumption_resolution,[],[f69,f24])).
% 1.66/0.60  fof(f24,plain,(
% 1.66/0.60    v1_relat_1(sK0)),
% 1.66/0.60    inference(cnf_transformation,[],[f21])).
% 1.66/0.60  fof(f21,plain,(
% 1.66/0.60    ((~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.66/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20,f19,f18])).
% 1.66/0.60  fof(f18,plain,(
% 1.66/0.60    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f19,plain,(
% 1.66/0.60    ? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f20,plain,(
% 1.66/0.60    ? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(sK1,X2))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) & v1_relat_1(sK2))),
% 1.66/0.60    introduced(choice_axiom,[])).
% 1.66/0.60  fof(f13,plain,(
% 1.66/0.60    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f12])).
% 1.66/0.60  fof(f12,negated_conjecture,(
% 1.66/0.60    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))))))),
% 1.66/0.60    inference(negated_conjecture,[],[f11])).
% 1.66/0.60  fof(f11,conjecture,(
% 1.66/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))))))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relat_1)).
% 1.66/0.60  fof(f69,plain,(
% 1.66/0.60    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | ~v1_relat_1(sK0)),
% 1.66/0.60    inference(subsumption_resolution,[],[f68,f26])).
% 1.66/0.60  fof(f26,plain,(
% 1.66/0.60    v1_relat_1(sK2)),
% 1.66/0.60    inference(cnf_transformation,[],[f21])).
% 1.66/0.60  fof(f68,plain,(
% 1.66/0.60    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0)),
% 1.66/0.60    inference(subsumption_resolution,[],[f67,f45])).
% 1.66/0.60  fof(f45,plain,(
% 1.66/0.60    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK1,X0))) )),
% 1.66/0.60    inference(resolution,[],[f25,f35])).
% 1.66/0.60  fof(f35,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f17])).
% 1.66/0.60  fof(f17,plain,(
% 1.66/0.60    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f9])).
% 1.66/0.60  fof(f9,axiom,(
% 1.66/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 1.66/0.60  fof(f25,plain,(
% 1.66/0.60    v1_relat_1(sK1)),
% 1.66/0.60    inference(cnf_transformation,[],[f21])).
% 1.66/0.60  fof(f67,plain,(
% 1.66/0.60    ~r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | ~v1_relat_1(k4_xboole_0(sK1,sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0)),
% 1.66/0.60    inference(superposition,[],[f53,f34])).
% 1.66/0.60  fof(f34,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f16])).
% 1.66/0.60  fof(f16,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f10])).
% 1.66/0.60  fof(f10,axiom,(
% 1.66/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relat_1)).
% 1.66/0.60  fof(f53,plain,(
% 1.66/0.60    ~r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k4_xboole_0(sK1,sK2))))),
% 1.66/0.60    inference(resolution,[],[f40,f28])).
% 1.66/0.60  fof(f28,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f14])).
% 1.66/0.60  fof(f14,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.66/0.60    inference(ennf_transformation,[],[f4])).
% 1.66/0.60  fof(f4,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.66/0.60  fof(f40,plain,(
% 1.66/0.60    ~r1_tarski(k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k4_xboole_0(sK1,sK2)))),
% 1.66/0.60    inference(forward_demodulation,[],[f39,f33])).
% 1.66/0.60  fof(f33,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f8])).
% 1.66/0.60  fof(f8,axiom,(
% 1.66/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.66/0.60  fof(f39,plain,(
% 1.66/0.60    ~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k4_xboole_0(sK1,sK2)))),
% 1.66/0.60    inference(forward_demodulation,[],[f27,f33])).
% 1.66/0.60  fof(f27,plain,(
% 1.66/0.60    ~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))),
% 1.66/0.60    inference(cnf_transformation,[],[f21])).
% 1.66/0.60  fof(f457,plain,(
% 1.66/0.60    r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1)))),
% 1.66/0.60    inference(resolution,[],[f451,f38])).
% 1.66/0.60  fof(f38,plain,(
% 1.66/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.60    inference(equality_resolution,[],[f30])).
% 1.66/0.60  fof(f30,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.66/0.60    inference(cnf_transformation,[],[f23])).
% 1.66/0.60  fof(f23,plain,(
% 1.66/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.60    inference(flattening,[],[f22])).
% 1.66/0.60  fof(f22,plain,(
% 1.66/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.60    inference(nnf_transformation,[],[f1])).
% 1.66/0.60  fof(f1,axiom,(
% 1.66/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.60  fof(f451,plain,(
% 1.66/0.60    ( ! [X0] : (~r1_tarski(X0,k5_relat_1(sK0,sK1)) | r1_tarski(X0,k5_relat_1(sK0,k2_xboole_0(sK2,sK1)))) )),
% 1.66/0.60    inference(superposition,[],[f29,f241])).
% 1.66/0.60  fof(f241,plain,(
% 1.66/0.60    k5_relat_1(sK0,k2_xboole_0(sK2,sK1)) = k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,sK1))),
% 1.66/0.60    inference(resolution,[],[f82,f26])).
% 1.66/0.60  fof(f82,plain,(
% 1.66/0.60    ( ! [X13] : (~v1_relat_1(X13) | k5_relat_1(sK0,k2_xboole_0(X13,sK1)) = k2_xboole_0(k5_relat_1(sK0,X13),k5_relat_1(sK0,sK1))) )),
% 1.66/0.60    inference(resolution,[],[f42,f25])).
% 1.66/0.60  fof(f42,plain,(
% 1.66/0.60    ( ! [X2,X1] : (~v1_relat_1(X2) | k5_relat_1(sK0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)) | ~v1_relat_1(X1)) )),
% 1.66/0.60    inference(resolution,[],[f24,f34])).
% 1.66/0.60  fof(f29,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f15])).
% 1.66/0.60  fof(f15,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.66/0.60    inference(ennf_transformation,[],[f2])).
% 1.66/0.60  fof(f2,axiom,(
% 1.66/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.66/0.60  % SZS output end Proof for theBenchmark
% 1.66/0.60  % (23102)------------------------------
% 1.66/0.60  % (23102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (23102)Termination reason: Refutation
% 1.66/0.60  
% 1.66/0.60  % (23102)Memory used [KB]: 11385
% 1.66/0.60  % (23102)Time elapsed: 0.175 s
% 1.66/0.60  % (23102)------------------------------
% 1.66/0.60  % (23102)------------------------------
% 1.86/0.60  % (23088)Success in time 0.237 s
%------------------------------------------------------------------------------
