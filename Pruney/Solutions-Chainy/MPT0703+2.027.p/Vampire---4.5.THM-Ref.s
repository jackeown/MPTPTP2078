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
% DateTime   : Thu Dec  3 12:54:22 EST 2020

% Result     : Theorem 4.38s
% Output     : Refutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 246 expanded)
%              Number of leaves         :   12 (  60 expanded)
%              Depth                    :   21
%              Number of atoms          :  157 ( 618 expanded)
%              Number of equality atoms :   26 (  74 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10415,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f9099,f10414])).

fof(f10414,plain,(
    ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f10408])).

fof(f10408,plain,
    ( $false
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f48,f10407])).

fof(f10407,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl3_19 ),
    inference(duplicate_literal_removal,[],[f10406])).

fof(f10406,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_19 ),
    inference(superposition,[],[f10398,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f10398,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK1),sK1)
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f48,f10374,f209])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f111,f37])).

fof(f111,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),sK1)
      | ~ r1_tarski(sK0,X1) ) ),
    inference(superposition,[],[f62,f37])).

fof(f62,plain,(
    ! [X0,X1] : ~ r1_tarski(k2_xboole_0(k2_xboole_0(sK0,X0),X1),sK1) ),
    inference(unit_resulting_resolution,[],[f54,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f54,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f30,f32])).

fof(f30,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f10374,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK1))
    | ~ spl3_19 ),
    inference(superposition,[],[f6129,f9102])).

fof(f9102,plain,
    ( sK1 = k2_xboole_0(k6_subset_1(sK0,sK0),sK1)
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f7898,f37])).

fof(f7898,plain,
    ( r1_tarski(k6_subset_1(sK0,sK0),sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f7897])).

fof(f7897,plain,
    ( spl3_19
  <=> r1_tarski(k6_subset_1(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f6129,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,k2_xboole_0(k6_subset_1(sK0,sK0),X0))) ),
    inference(unit_resulting_resolution,[],[f38,f4982])).

fof(f4982,plain,(
    ! [X2] :
      ( r1_tarski(sK0,k2_xboole_0(sK1,X2))
      | ~ r1_tarski(k6_subset_1(sK0,sK0),X2) ) ),
    inference(superposition,[],[f45,f4778])).

fof(f4778,plain,(
    k6_subset_1(sK0,sK1) = k6_subset_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f2169,f2171])).

fof(f2171,plain,(
    k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(sK0,k2_relat_1(sK2))) ),
    inference(superposition,[],[f92,f1170])).

fof(f1170,plain,(
    ! [X0] : k6_subset_1(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k6_subset_1(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f121,f1146,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1146,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(sK2,k6_subset_1(X0,X0)),X1) ),
    inference(unit_resulting_resolution,[],[f38,f480])).

fof(f480,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k10_relat_1(sK2,X1),k2_xboole_0(k10_relat_1(sK2,X2),X3))
      | r1_tarski(k10_relat_1(sK2,k6_subset_1(X1,X2)),X3) ) ),
    inference(superposition,[],[f46,f49])).

fof(f49,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(unit_resulting_resolution,[],[f26,f27,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f121,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,k2_relat_1(sK2)),X0) ),
    inference(unit_resulting_resolution,[],[f116,f46])).

fof(f116,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(k2_relat_1(sK2),X0)) ),
    inference(unit_resulting_resolution,[],[f38,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f32,f57])).

fof(f57,plain,(
    k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f29,f37])).

fof(f29,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,(
    ! [X0] : k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0))) ),
    inference(unit_resulting_resolution,[],[f26,f27,f64,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f58,f46])).

fof(f58,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f29,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f2169,plain,(
    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(sK0,k2_relat_1(sK2))) ),
    inference(superposition,[],[f92,f619])).

fof(f619,plain,(
    k6_subset_1(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f121,f604,f36])).

fof(f604,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0) ),
    inference(forward_demodulation,[],[f596,f49])).

fof(f596,plain,(
    ! [X0] : r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),X0) ),
    inference(unit_resulting_resolution,[],[f592,f46])).

fof(f592,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f38,f344])).

fof(f344,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK1),X0)
      | r1_tarski(k10_relat_1(sK2,sK0),X0) ) ),
    inference(superposition,[],[f32,f83])).

fof(f83,plain,(
    k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f28,f37])).

fof(f28,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f9099,plain,(
    spl3_19 ),
    inference(avatar_contradiction_clause,[],[f9096])).

fof(f9096,plain,
    ( $false
    | spl3_19 ),
    inference(unit_resulting_resolution,[],[f38,f7899,f46])).

fof(f7899,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK0),sK1)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f7897])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:13:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (18163)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.50  % (18160)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (18170)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (18163)Refutation not found, incomplete strategy% (18163)------------------------------
% 0.22/0.52  % (18163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18163)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18163)Memory used [KB]: 10618
% 0.22/0.52  % (18163)Time elapsed: 0.079 s
% 0.22/0.52  % (18163)------------------------------
% 0.22/0.52  % (18163)------------------------------
% 0.22/0.52  % (18161)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (18159)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (18159)Refutation not found, incomplete strategy% (18159)------------------------------
% 0.22/0.53  % (18159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18159)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18159)Memory used [KB]: 10618
% 0.22/0.53  % (18159)Time elapsed: 0.106 s
% 0.22/0.53  % (18159)------------------------------
% 0.22/0.53  % (18159)------------------------------
% 0.22/0.53  % (18153)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (18149)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (18150)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (18152)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (18147)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (18151)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (18173)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.55  % (18169)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.55  % (18158)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.39/0.55  % (18175)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.39/0.55  % (18166)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.55  % (18162)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.55  % (18165)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.55  % (18177)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.55  % (18177)Refutation not found, incomplete strategy% (18177)------------------------------
% 1.39/0.55  % (18177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (18177)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (18177)Memory used [KB]: 1663
% 1.39/0.55  % (18177)Time elapsed: 0.001 s
% 1.39/0.55  % (18177)------------------------------
% 1.39/0.55  % (18177)------------------------------
% 1.39/0.56  % (18174)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.56  % (18156)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.56  % (18154)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.56  % (18157)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.56  % (18148)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.39/0.56  % (18148)Refutation not found, incomplete strategy% (18148)------------------------------
% 1.39/0.56  % (18148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (18148)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (18148)Memory used [KB]: 1663
% 1.39/0.56  % (18148)Time elapsed: 0.143 s
% 1.39/0.56  % (18148)------------------------------
% 1.39/0.56  % (18148)------------------------------
% 1.39/0.56  % (18171)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.56  % (18168)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.55/0.58  % (18172)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.55/0.58  % (18157)Refutation not found, incomplete strategy% (18157)------------------------------
% 1.55/0.58  % (18157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (18157)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (18157)Memory used [KB]: 10746
% 1.55/0.58  % (18157)Time elapsed: 0.149 s
% 1.55/0.58  % (18157)------------------------------
% 1.55/0.58  % (18157)------------------------------
% 1.55/0.58  % (18155)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.55/0.59  % (18164)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.55/0.60  % (18203)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.55/0.61  % (18176)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.55/0.61  % (18176)Refutation not found, incomplete strategy% (18176)------------------------------
% 1.55/0.61  % (18176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.61  % (18176)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.61  
% 1.55/0.61  % (18176)Memory used [KB]: 10746
% 1.55/0.61  % (18176)Time elapsed: 0.198 s
% 1.55/0.61  % (18176)------------------------------
% 1.55/0.61  % (18176)------------------------------
% 2.22/0.66  % (18204)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.22/0.67  % (18150)Refutation not found, incomplete strategy% (18150)------------------------------
% 2.22/0.67  % (18150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.67  % (18150)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.67  
% 2.22/0.67  % (18150)Memory used [KB]: 6140
% 2.22/0.67  % (18150)Time elapsed: 0.255 s
% 2.22/0.67  % (18150)------------------------------
% 2.22/0.67  % (18150)------------------------------
% 2.22/0.68  % (18205)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.22/0.68  % (18205)Refutation not found, incomplete strategy% (18205)------------------------------
% 2.22/0.68  % (18205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (18205)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.68  
% 2.22/0.68  % (18205)Memory used [KB]: 6140
% 2.22/0.68  % (18205)Time elapsed: 0.100 s
% 2.22/0.68  % (18205)------------------------------
% 2.22/0.68  % (18205)------------------------------
% 2.22/0.68  % (18147)Refutation not found, incomplete strategy% (18147)------------------------------
% 2.22/0.68  % (18147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (18147)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.68  
% 2.22/0.68  % (18147)Memory used [KB]: 1663
% 2.22/0.68  % (18147)Time elapsed: 0.265 s
% 2.22/0.68  % (18147)------------------------------
% 2.22/0.68  % (18147)------------------------------
% 2.22/0.69  % (18162)Refutation not found, incomplete strategy% (18162)------------------------------
% 2.22/0.69  % (18162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.69  % (18162)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.69  
% 2.22/0.69  % (18162)Memory used [KB]: 6140
% 2.22/0.69  % (18162)Time elapsed: 0.259 s
% 2.22/0.69  % (18162)------------------------------
% 2.22/0.69  % (18162)------------------------------
% 2.22/0.72  % (18206)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.22/0.72  % (18207)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.71/0.75  % (18208)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.91/0.81  % (18214)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.91/0.81  % (18172)Time limit reached!
% 2.91/0.81  % (18172)------------------------------
% 2.91/0.81  % (18172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.81  % (18172)Termination reason: Time limit
% 2.91/0.81  % (18172)Termination phase: Saturation
% 2.91/0.81  
% 2.91/0.81  % (18172)Memory used [KB]: 13560
% 2.91/0.81  % (18172)Time elapsed: 0.400 s
% 2.91/0.81  % (18172)------------------------------
% 2.91/0.81  % (18172)------------------------------
% 2.91/0.82  % (18215)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.32/0.84  % (18216)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.32/0.85  % (18149)Time limit reached!
% 3.32/0.85  % (18149)------------------------------
% 3.32/0.85  % (18149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.85  % (18219)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.32/0.86  % (18149)Termination reason: Time limit
% 3.32/0.86  
% 3.32/0.86  % (18149)Memory used [KB]: 7164
% 3.32/0.86  % (18149)Time elapsed: 0.426 s
% 3.32/0.86  % (18149)------------------------------
% 3.32/0.86  % (18149)------------------------------
% 3.85/0.94  % (18224)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.04/0.97  % (18153)Time limit reached!
% 4.04/0.97  % (18153)------------------------------
% 4.04/0.97  % (18153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.04/0.97  % (18153)Termination reason: Time limit
% 4.04/0.97  
% 4.04/0.97  % (18153)Memory used [KB]: 16375
% 4.04/0.97  % (18153)Time elapsed: 0.505 s
% 4.04/0.97  % (18153)------------------------------
% 4.04/0.97  % (18153)------------------------------
% 4.04/0.97  % (18161)Time limit reached!
% 4.04/0.97  % (18161)------------------------------
% 4.04/0.97  % (18161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.04/0.97  % (18161)Termination reason: Time limit
% 4.04/0.97  % (18161)Termination phase: Saturation
% 4.04/0.97  
% 4.04/0.97  % (18161)Memory used [KB]: 5245
% 4.04/0.97  % (18161)Time elapsed: 0.500 s
% 4.04/0.97  % (18161)------------------------------
% 4.04/0.97  % (18161)------------------------------
% 4.04/0.98  % (18225)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 4.38/1.03  % (18154)Time limit reached!
% 4.38/1.03  % (18154)------------------------------
% 4.38/1.03  % (18154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.38/1.03  % (18154)Termination reason: Time limit
% 4.38/1.03  
% 4.38/1.03  % (18154)Memory used [KB]: 6140
% 4.38/1.03  % (18154)Time elapsed: 0.618 s
% 4.38/1.03  % (18154)------------------------------
% 4.38/1.03  % (18154)------------------------------
% 4.38/1.06  % (18173)Refutation found. Thanks to Tanya!
% 4.38/1.06  % SZS status Theorem for theBenchmark
% 4.38/1.06  % SZS output start Proof for theBenchmark
% 4.38/1.06  fof(f10415,plain,(
% 4.38/1.06    $false),
% 4.38/1.06    inference(avatar_sat_refutation,[],[f9099,f10414])).
% 4.38/1.06  fof(f10414,plain,(
% 4.38/1.06    ~spl3_19),
% 4.38/1.06    inference(avatar_contradiction_clause,[],[f10408])).
% 4.38/1.06  fof(f10408,plain,(
% 4.38/1.06    $false | ~spl3_19),
% 4.38/1.06    inference(unit_resulting_resolution,[],[f48,f10407])).
% 4.38/1.06  fof(f10407,plain,(
% 4.38/1.06    ~r1_tarski(sK1,sK1) | ~spl3_19),
% 4.38/1.06    inference(duplicate_literal_removal,[],[f10406])).
% 4.38/1.06  fof(f10406,plain,(
% 4.38/1.06    ~r1_tarski(sK1,sK1) | ~r1_tarski(sK1,sK1) | ~spl3_19),
% 4.38/1.06    inference(superposition,[],[f10398,f37])).
% 4.38/1.06  fof(f37,plain,(
% 4.38/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.38/1.06    inference(cnf_transformation,[],[f20])).
% 4.38/1.06  fof(f20,plain,(
% 4.38/1.06    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.38/1.06    inference(ennf_transformation,[],[f4])).
% 4.38/1.06  fof(f4,axiom,(
% 4.38/1.06    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.38/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.38/1.06  fof(f10398,plain,(
% 4.38/1.06    ~r1_tarski(k2_xboole_0(sK1,sK1),sK1) | ~spl3_19),
% 4.38/1.06    inference(unit_resulting_resolution,[],[f48,f10374,f209])).
% 4.38/1.06  fof(f209,plain,(
% 4.38/1.06    ( ! [X0,X1] : (~r1_tarski(X1,sK1) | ~r1_tarski(sK0,X0) | ~r1_tarski(X0,X1)) )),
% 4.38/1.06    inference(superposition,[],[f111,f37])).
% 4.38/1.06  fof(f111,plain,(
% 4.38/1.06    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),sK1) | ~r1_tarski(sK0,X1)) )),
% 4.38/1.06    inference(superposition,[],[f62,f37])).
% 4.38/1.06  fof(f62,plain,(
% 4.38/1.06    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k2_xboole_0(sK0,X0),X1),sK1)) )),
% 4.38/1.06    inference(unit_resulting_resolution,[],[f54,f32])).
% 4.38/1.06  fof(f32,plain,(
% 4.38/1.06    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 4.38/1.06    inference(cnf_transformation,[],[f18])).
% 4.38/1.06  fof(f18,plain,(
% 4.38/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 4.38/1.06    inference(ennf_transformation,[],[f3])).
% 4.38/1.06  fof(f3,axiom,(
% 4.38/1.06    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 4.38/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 4.38/1.06  fof(f54,plain,(
% 4.38/1.06    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),sK1)) )),
% 4.38/1.06    inference(unit_resulting_resolution,[],[f30,f32])).
% 4.38/1.06  fof(f30,plain,(
% 4.38/1.06    ~r1_tarski(sK0,sK1)),
% 4.38/1.06    inference(cnf_transformation,[],[f15])).
% 4.38/1.06  fof(f15,plain,(
% 4.38/1.06    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 4.38/1.06    inference(flattening,[],[f14])).
% 4.38/1.06  fof(f14,plain,(
% 4.38/1.06    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 4.38/1.06    inference(ennf_transformation,[],[f13])).
% 4.38/1.06  fof(f13,negated_conjecture,(
% 4.38/1.06    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 4.38/1.06    inference(negated_conjecture,[],[f12])).
% 4.38/1.06  fof(f12,conjecture,(
% 4.38/1.06    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 4.38/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 4.38/1.06  fof(f10374,plain,(
% 4.38/1.06    r1_tarski(sK0,k2_xboole_0(sK1,sK1)) | ~spl3_19),
% 4.38/1.06    inference(superposition,[],[f6129,f9102])).
% 4.38/1.06  fof(f9102,plain,(
% 4.38/1.06    sK1 = k2_xboole_0(k6_subset_1(sK0,sK0),sK1) | ~spl3_19),
% 4.38/1.06    inference(unit_resulting_resolution,[],[f7898,f37])).
% 4.38/1.06  fof(f7898,plain,(
% 4.38/1.06    r1_tarski(k6_subset_1(sK0,sK0),sK1) | ~spl3_19),
% 4.38/1.06    inference(avatar_component_clause,[],[f7897])).
% 4.38/1.06  fof(f7897,plain,(
% 4.38/1.06    spl3_19 <=> r1_tarski(k6_subset_1(sK0,sK0),sK1)),
% 4.38/1.06    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 4.38/1.06  fof(f6129,plain,(
% 4.38/1.06    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,k2_xboole_0(k6_subset_1(sK0,sK0),X0)))) )),
% 4.38/1.06    inference(unit_resulting_resolution,[],[f38,f4982])).
% 4.38/1.06  fof(f4982,plain,(
% 4.38/1.06    ( ! [X2] : (r1_tarski(sK0,k2_xboole_0(sK1,X2)) | ~r1_tarski(k6_subset_1(sK0,sK0),X2)) )),
% 4.38/1.06    inference(superposition,[],[f45,f4778])).
% 4.38/1.06  fof(f4778,plain,(
% 4.38/1.06    k6_subset_1(sK0,sK1) = k6_subset_1(sK0,sK0)),
% 4.38/1.06    inference(backward_demodulation,[],[f2169,f2171])).
% 4.38/1.06  fof(f2171,plain,(
% 4.38/1.06    k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(sK0,k2_relat_1(sK2)))),
% 4.38/1.06    inference(superposition,[],[f92,f1170])).
% 4.38/1.07  fof(f1170,plain,(
% 4.38/1.07    ( ! [X0] : (k6_subset_1(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k6_subset_1(X0,X0))) )),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f121,f1146,f36])).
% 4.38/1.07  fof(f36,plain,(
% 4.38/1.07    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 4.38/1.07    inference(cnf_transformation,[],[f1])).
% 4.38/1.07  fof(f1,axiom,(
% 4.38/1.07    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.38/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.38/1.07  fof(f1146,plain,(
% 4.38/1.07    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(X0,X0)),X1)) )),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f38,f480])).
% 4.38/1.07  fof(f480,plain,(
% 4.38/1.07    ( ! [X2,X3,X1] : (~r1_tarski(k10_relat_1(sK2,X1),k2_xboole_0(k10_relat_1(sK2,X2),X3)) | r1_tarski(k10_relat_1(sK2,k6_subset_1(X1,X2)),X3)) )),
% 4.38/1.07    inference(superposition,[],[f46,f49])).
% 4.38/1.07  fof(f49,plain,(
% 4.38/1.07    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f26,f27,f39])).
% 4.38/1.07  fof(f39,plain,(
% 4.38/1.07    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 4.38/1.07    inference(cnf_transformation,[],[f22])).
% 4.38/1.07  fof(f22,plain,(
% 4.38/1.07    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.38/1.07    inference(flattening,[],[f21])).
% 4.38/1.07  fof(f21,plain,(
% 4.38/1.07    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.38/1.07    inference(ennf_transformation,[],[f10])).
% 4.38/1.07  fof(f10,axiom,(
% 4.38/1.07    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 4.38/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 4.38/1.07  fof(f27,plain,(
% 4.38/1.07    v1_funct_1(sK2)),
% 4.38/1.07    inference(cnf_transformation,[],[f15])).
% 4.38/1.07  fof(f26,plain,(
% 4.38/1.07    v1_relat_1(sK2)),
% 4.38/1.07    inference(cnf_transformation,[],[f15])).
% 4.38/1.07  fof(f46,plain,(
% 4.38/1.07    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.38/1.07    inference(definition_unfolding,[],[f42,f43])).
% 4.38/1.07  fof(f43,plain,(
% 4.38/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 4.38/1.07    inference(cnf_transformation,[],[f9])).
% 4.38/1.07  fof(f9,axiom,(
% 4.38/1.07    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 4.38/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 4.38/1.07  fof(f42,plain,(
% 4.38/1.07    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 4.38/1.07    inference(cnf_transformation,[],[f25])).
% 4.38/1.07  fof(f25,plain,(
% 4.38/1.07    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.38/1.07    inference(ennf_transformation,[],[f5])).
% 4.38/1.07  fof(f5,axiom,(
% 4.38/1.07    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.38/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 4.38/1.07  fof(f121,plain,(
% 4.38/1.07    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,k2_relat_1(sK2)),X0)) )),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f116,f46])).
% 4.38/1.07  fof(f116,plain,(
% 4.38/1.07    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(k2_relat_1(sK2),X0))) )),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f38,f108])).
% 4.38/1.07  fof(f108,plain,(
% 4.38/1.07    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | r1_tarski(sK0,X0)) )),
% 4.38/1.07    inference(superposition,[],[f32,f57])).
% 4.38/1.07  fof(f57,plain,(
% 4.38/1.07    k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2))),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f29,f37])).
% 4.38/1.07  fof(f29,plain,(
% 4.38/1.07    r1_tarski(sK0,k2_relat_1(sK2))),
% 4.38/1.07    inference(cnf_transformation,[],[f15])).
% 4.38/1.07  fof(f92,plain,(
% 4.38/1.07    ( ! [X0] : (k6_subset_1(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X0)))) )),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f26,f27,f64,f31])).
% 4.38/1.07  fof(f31,plain,(
% 4.38/1.07    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 4.38/1.07    inference(cnf_transformation,[],[f17])).
% 4.38/1.07  fof(f17,plain,(
% 4.38/1.07    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.38/1.07    inference(flattening,[],[f16])).
% 4.38/1.07  fof(f16,plain,(
% 4.38/1.07    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.38/1.07    inference(ennf_transformation,[],[f11])).
% 4.38/1.07  fof(f11,axiom,(
% 4.38/1.07    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 4.38/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 4.38/1.07  fof(f64,plain,(
% 4.38/1.07    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2))) )),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f58,f46])).
% 4.38/1.07  fof(f58,plain,(
% 4.38/1.07    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,k2_relat_1(sK2)))) )),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f29,f33])).
% 4.38/1.07  fof(f33,plain,(
% 4.38/1.07    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 4.38/1.07    inference(cnf_transformation,[],[f19])).
% 4.38/1.07  fof(f19,plain,(
% 4.38/1.07    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 4.38/1.07    inference(ennf_transformation,[],[f2])).
% 4.38/1.07  fof(f2,axiom,(
% 4.38/1.07    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 4.38/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 4.38/1.07  fof(f2169,plain,(
% 4.38/1.07    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(sK0,k2_relat_1(sK2)))),
% 4.38/1.07    inference(superposition,[],[f92,f619])).
% 4.38/1.07  fof(f619,plain,(
% 4.38/1.07    k6_subset_1(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f121,f604,f36])).
% 4.38/1.07  fof(f604,plain,(
% 4.38/1.07    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0)) )),
% 4.38/1.07    inference(forward_demodulation,[],[f596,f49])).
% 4.38/1.07  fof(f596,plain,(
% 4.38/1.07    ( ! [X0] : (r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),X0)) )),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f592,f46])).
% 4.38/1.07  fof(f592,plain,(
% 4.38/1.07    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X0))) )),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f38,f344])).
% 4.38/1.07  fof(f344,plain,(
% 4.38/1.07    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,sK1),X0) | r1_tarski(k10_relat_1(sK2,sK0),X0)) )),
% 4.38/1.07    inference(superposition,[],[f32,f83])).
% 4.38/1.07  fof(f83,plain,(
% 4.38/1.07    k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f28,f37])).
% 4.38/1.07  fof(f28,plain,(
% 4.38/1.07    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 4.38/1.07    inference(cnf_transformation,[],[f15])).
% 4.38/1.07  fof(f45,plain,(
% 4.38/1.07    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.38/1.07    inference(definition_unfolding,[],[f41,f43])).
% 4.38/1.07  fof(f41,plain,(
% 4.38/1.07    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.38/1.07    inference(cnf_transformation,[],[f24])).
% 4.38/1.07  fof(f24,plain,(
% 4.38/1.07    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.38/1.07    inference(ennf_transformation,[],[f6])).
% 4.38/1.07  fof(f6,axiom,(
% 4.38/1.07    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.38/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 4.38/1.07  fof(f38,plain,(
% 4.38/1.07    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.38/1.07    inference(cnf_transformation,[],[f8])).
% 4.38/1.07  fof(f8,axiom,(
% 4.38/1.07    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.38/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.38/1.07  fof(f48,plain,(
% 4.38/1.07    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.38/1.07    inference(equality_resolution,[],[f34])).
% 4.38/1.07  fof(f34,plain,(
% 4.38/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.38/1.07    inference(cnf_transformation,[],[f1])).
% 4.38/1.07  fof(f9099,plain,(
% 4.38/1.07    spl3_19),
% 4.38/1.07    inference(avatar_contradiction_clause,[],[f9096])).
% 4.38/1.07  fof(f9096,plain,(
% 4.38/1.07    $false | spl3_19),
% 4.38/1.07    inference(unit_resulting_resolution,[],[f38,f7899,f46])).
% 4.38/1.07  fof(f7899,plain,(
% 4.38/1.07    ~r1_tarski(k6_subset_1(sK0,sK0),sK1) | spl3_19),
% 4.38/1.07    inference(avatar_component_clause,[],[f7897])).
% 4.38/1.07  % SZS output end Proof for theBenchmark
% 4.38/1.07  % (18173)------------------------------
% 4.38/1.07  % (18173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.38/1.07  % (18173)Termination reason: Refutation
% 4.38/1.07  
% 4.38/1.07  % (18173)Memory used [KB]: 8955
% 4.38/1.07  % (18173)Time elapsed: 0.650 s
% 4.38/1.07  % (18173)------------------------------
% 4.38/1.07  % (18173)------------------------------
% 4.38/1.07  % (18142)Success in time 0.688 s
%------------------------------------------------------------------------------
