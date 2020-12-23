%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:20 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 157 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  146 ( 583 expanded)
%              Number of equality atoms :   39 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f365,plain,(
    $false ),
    inference(subsumption_resolution,[],[f364,f52])).

fof(f52,plain,(
    k1_xboole_0 != k6_subset_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f31])).

% (23339)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (23338)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f28,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19])).

fof(f19,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f364,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f363,f267])).

fof(f267,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f87,f236])).

fof(f236,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f227,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f43,f41])).

% (23328)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f227,plain,(
    ! [X6] : k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X6,X6)) ),
    inference(superposition,[],[f90,f46])).

fof(f90,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(unit_resulting_resolution,[],[f24,f25,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f24,f25,f29,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f363,plain,(
    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f362,f24])).

fof(f362,plain,
    ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f361,f25])).

fof(f361,plain,
    ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f352,f76])).

fof(f76,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f40,f27,f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f27,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f352,plain,
    ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f32,f207])).

fof(f207,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f206,f24])).

fof(f206,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f199,f25])).

fof(f199,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f49,f38])).

fof(f49,plain,(
    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f26,f41])).

fof(f26,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:45:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.54  % (23312)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.55  % (23321)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (23313)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.55  % (23313)Refutation not found, incomplete strategy% (23313)------------------------------
% 0.20/0.55  % (23313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (23313)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (23313)Memory used [KB]: 1663
% 0.20/0.55  % (23313)Time elapsed: 0.141 s
% 0.20/0.55  % (23313)------------------------------
% 0.20/0.55  % (23313)------------------------------
% 0.20/0.56  % (23317)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.56  % (23315)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.56  % (23318)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (23319)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.57  % (23323)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.57  % (23322)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.52/0.57  % (23326)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.52/0.58  % (23316)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.52/0.58  % (23314)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.52/0.58  % (23327)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.52/0.58  % (23334)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.52/0.58  % (23333)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.52/0.58  % (23324)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.69/0.59  % (23320)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.69/0.59  % (23340)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.69/0.59  % (23341)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.69/0.60  % (23330)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.69/0.60  % (23332)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.69/0.60  % (23329)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.69/0.60  % (23336)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.69/0.60  % (23325)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.69/0.60  % (23316)Refutation found. Thanks to Tanya!
% 1.69/0.60  % SZS status Theorem for theBenchmark
% 1.69/0.60  % SZS output start Proof for theBenchmark
% 1.69/0.60  fof(f365,plain,(
% 1.69/0.60    $false),
% 1.69/0.60    inference(subsumption_resolution,[],[f364,f52])).
% 1.69/0.60  fof(f52,plain,(
% 1.69/0.60    k1_xboole_0 != k6_subset_1(sK0,sK1)),
% 1.69/0.60    inference(unit_resulting_resolution,[],[f28,f42])).
% 1.69/0.60  fof(f42,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.69/0.60    inference(definition_unfolding,[],[f36,f31])).
% 1.69/0.61  % (23339)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.69/0.61  % (23338)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.69/0.61  fof(f31,plain,(
% 1.69/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f6])).
% 1.69/0.61  fof(f6,axiom,(
% 1.69/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.69/0.61  fof(f36,plain,(
% 1.69/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.69/0.61    inference(cnf_transformation,[],[f23])).
% 1.69/0.61  fof(f23,plain,(
% 1.69/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.69/0.61    inference(nnf_transformation,[],[f2])).
% 1.69/0.61  fof(f2,axiom,(
% 1.69/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.69/0.61  fof(f28,plain,(
% 1.69/0.61    ~r1_tarski(sK0,sK1)),
% 1.69/0.61    inference(cnf_transformation,[],[f20])).
% 1.69/0.61  fof(f20,plain,(
% 1.69/0.61    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.69/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19])).
% 1.69/0.61  fof(f19,plain,(
% 1.69/0.61    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f12,plain,(
% 1.69/0.61    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.69/0.61    inference(flattening,[],[f11])).
% 1.69/0.61  fof(f11,plain,(
% 1.69/0.61    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.69/0.61    inference(ennf_transformation,[],[f10])).
% 1.69/0.61  fof(f10,negated_conjecture,(
% 1.69/0.61    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.69/0.61    inference(negated_conjecture,[],[f9])).
% 1.69/0.61  fof(f9,conjecture,(
% 1.69/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 1.69/0.61  fof(f364,plain,(
% 1.69/0.61    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 1.69/0.61    inference(forward_demodulation,[],[f363,f267])).
% 1.69/0.61  fof(f267,plain,(
% 1.69/0.61    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 1.69/0.61    inference(backward_demodulation,[],[f87,f236])).
% 1.69/0.61  fof(f236,plain,(
% 1.69/0.61    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 1.69/0.61    inference(forward_demodulation,[],[f227,f46])).
% 1.69/0.61  fof(f46,plain,(
% 1.69/0.61    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 1.69/0.61    inference(unit_resulting_resolution,[],[f43,f41])).
% 1.69/0.61  % (23328)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.69/0.61  fof(f41,plain,(
% 1.69/0.61    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.69/0.61    inference(definition_unfolding,[],[f37,f31])).
% 1.69/0.61  fof(f37,plain,(
% 1.69/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f23])).
% 1.69/0.61  fof(f43,plain,(
% 1.69/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.69/0.61    inference(equality_resolution,[],[f34])).
% 1.69/0.61  fof(f34,plain,(
% 1.69/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.69/0.61    inference(cnf_transformation,[],[f22])).
% 1.69/0.61  fof(f22,plain,(
% 1.69/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.61    inference(flattening,[],[f21])).
% 1.69/0.61  fof(f21,plain,(
% 1.69/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.61    inference(nnf_transformation,[],[f1])).
% 1.69/0.61  fof(f1,axiom,(
% 1.69/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.69/0.61  fof(f227,plain,(
% 1.69/0.61    ( ! [X6] : (k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X6,X6))) )),
% 1.69/0.61    inference(superposition,[],[f90,f46])).
% 1.69/0.61  fof(f90,plain,(
% 1.69/0.61    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 1.69/0.61    inference(unit_resulting_resolution,[],[f24,f25,f38])).
% 1.69/0.61  fof(f38,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f16])).
% 1.69/0.61  fof(f16,plain,(
% 1.69/0.61    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.69/0.61    inference(flattening,[],[f15])).
% 1.69/0.61  fof(f15,plain,(
% 1.69/0.61    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.69/0.61    inference(ennf_transformation,[],[f7])).
% 1.69/0.61  fof(f7,axiom,(
% 1.69/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 1.69/0.61  fof(f25,plain,(
% 1.69/0.61    v1_funct_1(sK2)),
% 1.69/0.61    inference(cnf_transformation,[],[f20])).
% 1.69/0.61  fof(f24,plain,(
% 1.69/0.61    v1_relat_1(sK2)),
% 1.69/0.61    inference(cnf_transformation,[],[f20])).
% 1.69/0.61  fof(f87,plain,(
% 1.69/0.61    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))),
% 1.69/0.61    inference(unit_resulting_resolution,[],[f24,f25,f29,f32])).
% 1.69/0.61  fof(f32,plain,(
% 1.69/0.61    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f14])).
% 1.69/0.61  fof(f14,plain,(
% 1.69/0.61    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.69/0.61    inference(flattening,[],[f13])).
% 1.69/0.61  fof(f13,plain,(
% 1.69/0.61    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.69/0.61    inference(ennf_transformation,[],[f8])).
% 1.69/0.61  fof(f8,axiom,(
% 1.69/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.69/0.61  fof(f29,plain,(
% 1.69/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f4])).
% 1.69/0.61  fof(f4,axiom,(
% 1.69/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.69/0.61  fof(f363,plain,(
% 1.69/0.61    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)),
% 1.69/0.61    inference(subsumption_resolution,[],[f362,f24])).
% 1.69/0.61  fof(f362,plain,(
% 1.69/0.61    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | ~v1_relat_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f361,f25])).
% 1.69/0.61  fof(f361,plain,(
% 1.69/0.61    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f352,f76])).
% 1.69/0.61  fof(f76,plain,(
% 1.69/0.61    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))) )),
% 1.69/0.61    inference(unit_resulting_resolution,[],[f40,f27,f39])).
% 1.69/0.61  fof(f39,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f18])).
% 1.69/0.61  fof(f18,plain,(
% 1.69/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.69/0.61    inference(flattening,[],[f17])).
% 1.69/0.61  fof(f17,plain,(
% 1.69/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.69/0.61    inference(ennf_transformation,[],[f3])).
% 1.69/0.61  fof(f3,axiom,(
% 1.69/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.69/0.61  fof(f27,plain,(
% 1.69/0.61    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.69/0.61    inference(cnf_transformation,[],[f20])).
% 1.69/0.61  fof(f40,plain,(
% 1.69/0.61    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.69/0.61    inference(definition_unfolding,[],[f30,f31])).
% 1.69/0.61  fof(f30,plain,(
% 1.69/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f5])).
% 1.69/0.61  fof(f5,axiom,(
% 1.69/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.69/0.61  fof(f352,plain,(
% 1.69/0.61    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.69/0.61    inference(superposition,[],[f32,f207])).
% 1.69/0.61  fof(f207,plain,(
% 1.69/0.61    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 1.69/0.61    inference(subsumption_resolution,[],[f206,f24])).
% 1.69/0.61  fof(f206,plain,(
% 1.69/0.61    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~v1_relat_1(sK2)),
% 1.69/0.61    inference(subsumption_resolution,[],[f199,f25])).
% 1.69/0.61  fof(f199,plain,(
% 1.69/0.61    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.69/0.61    inference(superposition,[],[f49,f38])).
% 1.69/0.61  fof(f49,plain,(
% 1.69/0.61    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.69/0.61    inference(unit_resulting_resolution,[],[f26,f41])).
% 1.69/0.61  fof(f26,plain,(
% 1.69/0.61    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.69/0.61    inference(cnf_transformation,[],[f20])).
% 1.69/0.61  % SZS output end Proof for theBenchmark
% 1.69/0.61  % (23316)------------------------------
% 1.69/0.61  % (23316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.61  % (23316)Termination reason: Refutation
% 1.69/0.61  
% 1.69/0.61  % (23316)Memory used [KB]: 1918
% 1.69/0.61  % (23316)Time elapsed: 0.191 s
% 1.69/0.61  % (23316)------------------------------
% 1.69/0.61  % (23316)------------------------------
% 1.69/0.61  % (23311)Success in time 0.244 s
%------------------------------------------------------------------------------
