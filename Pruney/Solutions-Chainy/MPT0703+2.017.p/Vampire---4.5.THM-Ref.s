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
% DateTime   : Thu Dec  3 12:54:20 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 179 expanded)
%              Number of leaves         :   11 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  152 ( 622 expanded)
%              Number of equality atoms :   45 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1054,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1046,f29])).

% (28942)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f29,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20])).

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

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

% (28935)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f1046,plain,(
    r1_tarski(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f1030])).

fof(f1030,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f44,f972])).

fof(f972,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f965,f351])).

fof(f351,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f350,f296])).

fof(f296,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f286,f66])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k6_subset_1(X1,X1) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f286,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f154,f66])).

% (28935)Refutation not found, incomplete strategy% (28935)------------------------------
% (28935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28935)Termination reason: Refutation not found, incomplete strategy

% (28935)Memory used [KB]: 1663
% (28935)Time elapsed: 0.157 s
% (28935)------------------------------
% (28935)------------------------------
fof(f154,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f153,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f153,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f41,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

% (28945)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f350,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f349,f25])).

fof(f349,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f128,f26])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f34,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f965,plain,(
    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) ),
    inference(superposition,[],[f201,f285])).

fof(f285,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f154,f70])).

fof(f70,plain,(
    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f43,f27])).

fof(f27,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f201,plain,(
    ! [X0] : k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) ),
    inference(subsumption_resolution,[],[f200,f25])).

fof(f200,plain,(
    ! [X0] :
      ( k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0)))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f192,f26])).

fof(f192,plain,(
    ! [X0] :
      ( k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f182,f34])).

fof(f182,plain,(
    ! [X7] : r1_tarski(k6_subset_1(sK0,X7),k2_relat_1(sK2)) ),
    inference(superposition,[],[f150,f50])).

fof(f50,plain,(
    k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f33,f28])).

fof(f28,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f150,plain,(
    ! [X6,X4,X5] : r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6)) ),
    inference(superposition,[],[f57,f49])).

fof(f49,plain,(
    ! [X2,X3] : k2_xboole_0(k6_subset_1(X2,X3),X2) = X2 ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f57,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f40,f45])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f32])).

% (28946)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:17:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.54  % (28941)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.54  % (28949)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.60/0.55  % (28957)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.60/0.56  % (28948)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.60/0.56  % (28940)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.60/0.56  % (28956)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.72/0.60  % (28951)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.72/0.60  % (28959)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.72/0.60  % (28934)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.72/0.60  % (28936)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.72/0.60  % (28943)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.72/0.61  % (28937)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.72/0.61  % (28955)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.72/0.61  % (28952)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.72/0.61  % (28958)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.72/0.61  % (28944)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.72/0.61  % (28963)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.72/0.61  % (28963)Refutation not found, incomplete strategy% (28963)------------------------------
% 1.72/0.61  % (28963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (28963)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.61  
% 1.72/0.61  % (28963)Memory used [KB]: 1663
% 1.72/0.61  % (28963)Time elapsed: 0.002 s
% 1.72/0.61  % (28963)------------------------------
% 1.72/0.61  % (28963)------------------------------
% 1.72/0.61  % (28944)Refutation not found, incomplete strategy% (28944)------------------------------
% 1.72/0.61  % (28944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (28944)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.61  
% 1.72/0.61  % (28944)Memory used [KB]: 10746
% 1.72/0.61  % (28944)Time elapsed: 0.194 s
% 1.72/0.61  % (28944)------------------------------
% 1.72/0.61  % (28944)------------------------------
% 1.72/0.61  % (28939)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.72/0.62  % (28961)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.72/0.62  % (28950)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.72/0.62  % (28947)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.72/0.62  % (28950)Refutation not found, incomplete strategy% (28950)------------------------------
% 1.72/0.62  % (28950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.62  % (28950)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.62  
% 1.72/0.62  % (28950)Memory used [KB]: 10618
% 1.72/0.62  % (28950)Time elapsed: 0.195 s
% 1.72/0.62  % (28950)------------------------------
% 1.72/0.62  % (28950)------------------------------
% 1.72/0.62  % (28960)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.72/0.62  % (28940)Refutation found. Thanks to Tanya!
% 1.72/0.62  % SZS status Theorem for theBenchmark
% 1.72/0.62  % SZS output start Proof for theBenchmark
% 1.72/0.62  fof(f1054,plain,(
% 1.72/0.62    $false),
% 1.72/0.62    inference(subsumption_resolution,[],[f1046,f29])).
% 1.72/0.62  % (28942)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.72/0.62  fof(f29,plain,(
% 1.72/0.62    ~r1_tarski(sK0,sK1)),
% 1.72/0.62    inference(cnf_transformation,[],[f21])).
% 1.72/0.62  fof(f21,plain,(
% 1.72/0.62    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.72/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20])).
% 1.72/0.62  fof(f20,plain,(
% 1.72/0.62    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.72/0.62    introduced(choice_axiom,[])).
% 1.72/0.62  fof(f13,plain,(
% 1.72/0.62    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.72/0.62    inference(flattening,[],[f12])).
% 1.72/0.62  fof(f12,plain,(
% 1.72/0.62    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.72/0.62    inference(ennf_transformation,[],[f11])).
% 1.72/0.62  fof(f11,negated_conjecture,(
% 1.72/0.62    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.72/0.62    inference(negated_conjecture,[],[f10])).
% 1.72/0.62  fof(f10,conjecture,(
% 1.72/0.62    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 1.72/0.62  % (28935)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.72/0.62  fof(f1046,plain,(
% 1.72/0.62    r1_tarski(sK0,sK1)),
% 1.72/0.62    inference(trivial_inequality_removal,[],[f1030])).
% 1.72/0.62  fof(f1030,plain,(
% 1.72/0.62    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1)),
% 1.72/0.62    inference(superposition,[],[f44,f972])).
% 1.72/0.62  fof(f972,plain,(
% 1.72/0.62    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 1.72/0.62    inference(forward_demodulation,[],[f965,f351])).
% 1.72/0.62  fof(f351,plain,(
% 1.72/0.62    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 1.72/0.62    inference(forward_demodulation,[],[f350,f296])).
% 1.72/0.62  fof(f296,plain,(
% 1.72/0.62    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 1.72/0.62    inference(forward_demodulation,[],[f286,f66])).
% 1.72/0.62  fof(f66,plain,(
% 1.72/0.62    ( ! [X1] : (k1_xboole_0 = k6_subset_1(X1,X1)) )),
% 1.72/0.62    inference(resolution,[],[f43,f45])).
% 1.72/0.62  fof(f45,plain,(
% 1.72/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.72/0.62    inference(equality_resolution,[],[f36])).
% 1.72/0.62  fof(f36,plain,(
% 1.72/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.72/0.62    inference(cnf_transformation,[],[f23])).
% 1.72/0.62  fof(f23,plain,(
% 1.72/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/0.62    inference(flattening,[],[f22])).
% 1.72/0.62  fof(f22,plain,(
% 1.72/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/0.62    inference(nnf_transformation,[],[f1])).
% 1.72/0.62  fof(f1,axiom,(
% 1.72/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.72/0.62  fof(f43,plain,(
% 1.72/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 1.72/0.62    inference(definition_unfolding,[],[f39,f32])).
% 1.72/0.62  fof(f32,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f7])).
% 1.72/0.62  fof(f7,axiom,(
% 1.72/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.72/0.62  fof(f39,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f24])).
% 1.72/0.62  fof(f24,plain,(
% 1.72/0.62    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.72/0.62    inference(nnf_transformation,[],[f2])).
% 1.72/0.62  fof(f2,axiom,(
% 1.72/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.72/0.62  fof(f286,plain,(
% 1.72/0.62    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X2,X2))) )),
% 1.72/0.62    inference(superposition,[],[f154,f66])).
% 1.72/0.62  % (28935)Refutation not found, incomplete strategy% (28935)------------------------------
% 1.72/0.62  % (28935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.62  % (28935)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.62  
% 1.72/0.62  % (28935)Memory used [KB]: 1663
% 1.72/0.62  % (28935)Time elapsed: 0.157 s
% 1.72/0.62  % (28935)------------------------------
% 1.72/0.62  % (28935)------------------------------
% 1.72/0.62  fof(f154,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f153,f25])).
% 1.72/0.62  fof(f25,plain,(
% 1.72/0.62    v1_relat_1(sK2)),
% 1.72/0.62    inference(cnf_transformation,[],[f21])).
% 1.72/0.62  fof(f153,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 1.72/0.62    inference(resolution,[],[f41,f26])).
% 1.72/0.62  fof(f26,plain,(
% 1.72/0.62    v1_funct_1(sK2)),
% 1.72/0.62    inference(cnf_transformation,[],[f21])).
% 1.72/0.62  fof(f41,plain,(
% 1.72/0.62    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f19])).
% 1.72/0.62  % (28945)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.72/0.62  fof(f19,plain,(
% 1.72/0.62    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.72/0.62    inference(flattening,[],[f18])).
% 1.72/0.62  fof(f18,plain,(
% 1.72/0.62    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.72/0.62    inference(ennf_transformation,[],[f8])).
% 1.72/0.62  fof(f8,axiom,(
% 1.72/0.62    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 1.72/0.62  fof(f350,plain,(
% 1.72/0.62    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0))),
% 1.72/0.62    inference(subsumption_resolution,[],[f349,f25])).
% 1.72/0.62  fof(f349,plain,(
% 1.72/0.62    k1_xboole_0 = k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) | ~v1_relat_1(sK2)),
% 1.72/0.62    inference(resolution,[],[f128,f26])).
% 1.72/0.62  fof(f128,plain,(
% 1.72/0.62    ( ! [X0] : (~v1_funct_1(X0) | k1_xboole_0 = k9_relat_1(X0,k10_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.72/0.62    inference(resolution,[],[f34,f30])).
% 1.72/0.62  fof(f30,plain,(
% 1.72/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f5])).
% 1.72/0.62  fof(f5,axiom,(
% 1.72/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.72/0.62  fof(f34,plain,(
% 1.72/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f16])).
% 1.72/0.62  fof(f16,plain,(
% 1.72/0.62    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.72/0.62    inference(flattening,[],[f15])).
% 1.72/0.62  fof(f15,plain,(
% 1.72/0.62    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.72/0.62    inference(ennf_transformation,[],[f9])).
% 1.72/0.62  fof(f9,axiom,(
% 1.72/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.72/0.62  fof(f965,plain,(
% 1.72/0.62    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)),
% 1.72/0.62    inference(superposition,[],[f201,f285])).
% 1.72/0.62  fof(f285,plain,(
% 1.72/0.62    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 1.72/0.62    inference(superposition,[],[f154,f70])).
% 1.72/0.62  fof(f70,plain,(
% 1.72/0.62    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.72/0.62    inference(resolution,[],[f43,f27])).
% 1.72/0.62  fof(f27,plain,(
% 1.72/0.62    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.72/0.62    inference(cnf_transformation,[],[f21])).
% 1.72/0.62  fof(f201,plain,(
% 1.72/0.62    ( ! [X0] : (k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0)))) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f200,f25])).
% 1.72/0.62  fof(f200,plain,(
% 1.72/0.62    ( ! [X0] : (k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) | ~v1_relat_1(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f192,f26])).
% 1.72/0.62  fof(f192,plain,(
% 1.72/0.62    ( ! [X0] : (k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.72/0.62    inference(resolution,[],[f182,f34])).
% 1.72/0.62  fof(f182,plain,(
% 1.72/0.62    ( ! [X7] : (r1_tarski(k6_subset_1(sK0,X7),k2_relat_1(sK2))) )),
% 1.72/0.62    inference(superposition,[],[f150,f50])).
% 1.72/0.62  fof(f50,plain,(
% 1.72/0.62    k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2))),
% 1.72/0.62    inference(resolution,[],[f33,f28])).
% 1.72/0.62  fof(f28,plain,(
% 1.72/0.62    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.72/0.62    inference(cnf_transformation,[],[f21])).
% 1.72/0.62  fof(f33,plain,(
% 1.72/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.72/0.62    inference(cnf_transformation,[],[f14])).
% 1.72/0.62  fof(f14,plain,(
% 1.72/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.72/0.62    inference(ennf_transformation,[],[f4])).
% 1.72/0.62  fof(f4,axiom,(
% 1.72/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.72/0.62  fof(f150,plain,(
% 1.72/0.62    ( ! [X6,X4,X5] : (r1_tarski(k6_subset_1(X4,X5),k2_xboole_0(X4,X6))) )),
% 1.72/0.62    inference(superposition,[],[f57,f49])).
% 1.72/0.62  fof(f49,plain,(
% 1.72/0.62    ( ! [X2,X3] : (k2_xboole_0(k6_subset_1(X2,X3),X2) = X2) )),
% 1.72/0.62    inference(resolution,[],[f33,f42])).
% 1.72/0.62  fof(f42,plain,(
% 1.72/0.62    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.72/0.62    inference(definition_unfolding,[],[f31,f32])).
% 1.72/0.62  fof(f31,plain,(
% 1.72/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f6])).
% 1.72/0.62  fof(f6,axiom,(
% 1.72/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.72/0.62  fof(f57,plain,(
% 1.72/0.62    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 1.72/0.62    inference(resolution,[],[f52,f40])).
% 1.72/0.62  fof(f40,plain,(
% 1.72/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f17])).
% 1.72/0.62  fof(f17,plain,(
% 1.72/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.72/0.62    inference(ennf_transformation,[],[f3])).
% 1.72/0.62  fof(f3,axiom,(
% 1.72/0.62    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.72/0.62  fof(f52,plain,(
% 1.72/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.72/0.62    inference(resolution,[],[f40,f45])).
% 1.72/0.62  fof(f44,plain,(
% 1.72/0.62    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.72/0.62    inference(definition_unfolding,[],[f38,f32])).
% 1.72/0.62  % (28946)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.72/0.62  fof(f38,plain,(
% 1.72/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.72/0.62    inference(cnf_transformation,[],[f24])).
% 1.72/0.62  % SZS output end Proof for theBenchmark
% 1.72/0.62  % (28940)------------------------------
% 1.72/0.62  % (28940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.62  % (28940)Termination reason: Refutation
% 1.72/0.62  
% 1.72/0.62  % (28940)Memory used [KB]: 11129
% 1.72/0.62  % (28940)Time elapsed: 0.177 s
% 1.72/0.62  % (28940)------------------------------
% 1.72/0.62  % (28940)------------------------------
% 1.72/0.63  % (28933)Success in time 0.278 s
%------------------------------------------------------------------------------
