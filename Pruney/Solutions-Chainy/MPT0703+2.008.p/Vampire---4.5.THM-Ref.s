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
% DateTime   : Thu Dec  3 12:54:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 128 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  207 ( 385 expanded)
%              Number of equality atoms :   36 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4055,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f447,f680,f3765,f3803,f4054])).

fof(f4054,plain,
    ( spl3_1
    | ~ spl3_56 ),
    inference(avatar_contradiction_clause,[],[f4053])).

fof(f4053,plain,
    ( $false
    | spl3_1
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f4025,f59])).

fof(f59,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f4025,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_56 ),
    inference(superposition,[],[f230,f3722])).

fof(f3722,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f3720])).

fof(f3720,plain,
    ( spl3_56
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f230,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f162,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f162,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(superposition,[],[f46,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f3803,plain,
    ( spl3_56
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f3798,f1907,f3720])).

fof(f1907,plain,
    ( spl3_53
  <=> r1_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f3798,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_53 ),
    inference(resolution,[],[f1909,f156])).

fof(f156,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,k4_xboole_0(X2,X3))
      | k3_xboole_0(X2,X3) = X2 ) ),
    inference(superposition,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f1909,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f1907])).

fof(f3765,plain,
    ( ~ spl3_2
    | ~ spl3_28
    | spl3_53 ),
    inference(avatar_contradiction_clause,[],[f3761])).

fof(f3761,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_28
    | spl3_53 ),
    inference(unit_resulting_resolution,[],[f64,f679,f1908,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f1908,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl3_53 ),
    inference(avatar_component_clause,[],[f1907])).

fof(f679,plain,
    ( r1_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f677])).

fof(f677,plain,
    ( spl3_28
  <=> r1_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f64,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f680,plain,
    ( spl3_28
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f675,f444,f77,f677])).

fof(f77,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f444,plain,
    ( spl3_24
  <=> k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f675,plain,
    ( r1_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f648,f79])).

fof(f79,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f648,plain,
    ( r1_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f641])).

fof(f641,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl3_24 ),
    inference(superposition,[],[f37,f446])).

fof(f446,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f444])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f447,plain,
    ( spl3_24
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f442,f77,f72,f67,f444])).

fof(f67,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f72,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

% (25045)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f442,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f441,f79])).

fof(f441,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f433,f74])).

fof(f74,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f433,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f189,f69])).

fof(f69,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f189,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k10_relat_1(X6,X7),k10_relat_1(X6,X8))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | k1_xboole_0 = k10_relat_1(X6,k4_xboole_0(X7,X8)) ) ),
    inference(superposition,[],[f185,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f184,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f47,f51])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f25])).

fof(f25,plain,
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

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f75,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f72])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f67])).

fof(f34,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f57])).

fof(f36,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (25058)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.49  % (25050)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (25041)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (25042)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (25064)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (25040)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (25060)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (25059)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (25065)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (25037)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (25061)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (25051)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (25049)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (25055)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (25053)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (25038)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (25043)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (25056)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (25052)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (25047)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (25066)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (25044)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (25048)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (25058)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f4055,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f447,f680,f3765,f3803,f4054])).
% 0.20/0.55  fof(f4054,plain,(
% 0.20/0.55    spl3_1 | ~spl3_56),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f4053])).
% 0.20/0.55  fof(f4053,plain,(
% 0.20/0.55    $false | (spl3_1 | ~spl3_56)),
% 0.20/0.55    inference(subsumption_resolution,[],[f4025,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.55  fof(f4025,plain,(
% 0.20/0.55    r1_tarski(sK0,sK1) | ~spl3_56),
% 0.20/0.55    inference(superposition,[],[f230,f3722])).
% 0.20/0.55  fof(f3722,plain,(
% 0.20/0.55    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_56),
% 0.20/0.55    inference(avatar_component_clause,[],[f3720])).
% 0.20/0.55  fof(f3720,plain,(
% 0.20/0.55    spl3_56 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.20/0.55    inference(superposition,[],[f162,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    ( ! [X8,X9] : (r1_tarski(k3_xboole_0(X8,X9),X8)) )),
% 0.20/0.55    inference(superposition,[],[f46,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.55  fof(f3803,plain,(
% 0.20/0.55    spl3_56 | ~spl3_53),
% 0.20/0.55    inference(avatar_split_clause,[],[f3798,f1907,f3720])).
% 0.20/0.55  fof(f1907,plain,(
% 0.20/0.55    spl3_53 <=> r1_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.20/0.55  fof(f3798,plain,(
% 0.20/0.55    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_53),
% 0.20/0.55    inference(resolution,[],[f1909,f156])).
% 0.20/0.55  fof(f156,plain,(
% 0.20/0.55    ( ! [X2,X3] : (~r1_xboole_0(X2,k4_xboole_0(X2,X3)) | k3_xboole_0(X2,X3) = X2) )),
% 0.20/0.55    inference(superposition,[],[f50,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.55    inference(nnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.55  fof(f1909,plain,(
% 0.20/0.55    r1_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_53),
% 0.20/0.55    inference(avatar_component_clause,[],[f1907])).
% 0.20/0.55  fof(f3765,plain,(
% 0.20/0.55    ~spl3_2 | ~spl3_28 | spl3_53),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f3761])).
% 0.20/0.55  fof(f3761,plain,(
% 0.20/0.55    $false | (~spl3_2 | ~spl3_28 | spl3_53)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f64,f679,f1908,f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(flattening,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.55  fof(f1908,plain,(
% 0.20/0.55    ~r1_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl3_53),
% 0.20/0.55    inference(avatar_component_clause,[],[f1907])).
% 0.20/0.55  fof(f679,plain,(
% 0.20/0.55    r1_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,sK1)) | ~spl3_28),
% 0.20/0.55    inference(avatar_component_clause,[],[f677])).
% 0.20/0.55  fof(f677,plain,(
% 0.20/0.55    spl3_28 <=> r1_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f62])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    spl3_2 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.55  fof(f680,plain,(
% 0.20/0.55    spl3_28 | ~spl3_5 | ~spl3_24),
% 0.20/0.55    inference(avatar_split_clause,[],[f675,f444,f77,f677])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    spl3_5 <=> v1_relat_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.55  fof(f444,plain,(
% 0.20/0.55    spl3_24 <=> k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.55  fof(f675,plain,(
% 0.20/0.55    r1_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,sK1)) | (~spl3_5 | ~spl3_24)),
% 0.20/0.55    inference(subsumption_resolution,[],[f648,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    v1_relat_1(sK2) | ~spl3_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f77])).
% 0.20/0.55  fof(f648,plain,(
% 0.20/0.55    r1_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,sK1)) | ~v1_relat_1(sK2) | ~spl3_24),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f641])).
% 0.20/0.55  fof(f641,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,sK1)) | ~v1_relat_1(sK2) | ~spl3_24),
% 0.20/0.55    inference(superposition,[],[f37,f446])).
% 0.20/0.55  fof(f446,plain,(
% 0.20/0.55    k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | ~spl3_24),
% 0.20/0.55    inference(avatar_component_clause,[],[f444])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.20/0.55  fof(f447,plain,(
% 0.20/0.55    spl3_24 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f442,f77,f72,f67,f444])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    spl3_3 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    spl3_4 <=> v1_funct_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.55  % (25045)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  fof(f442,plain,(
% 0.20/0.55    k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.20/0.55    inference(subsumption_resolution,[],[f441,f79])).
% 0.20/0.55  fof(f441,plain,(
% 0.20/0.55    ~v1_relat_1(sK2) | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f433,f74])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    v1_funct_1(sK2) | ~spl3_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f72])).
% 0.20/0.55  fof(f433,plain,(
% 0.20/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | ~spl3_3),
% 0.20/0.55    inference(resolution,[],[f189,f69])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f67])).
% 0.20/0.55  fof(f189,plain,(
% 0.20/0.55    ( ! [X6,X8,X7] : (~r1_tarski(k10_relat_1(X6,X7),k10_relat_1(X6,X8)) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_xboole_0 = k10_relat_1(X6,k4_xboole_0(X7,X8))) )),
% 0.20/0.55    inference(superposition,[],[f185,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.55    inference(nnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.55  fof(f185,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f184,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.55  fof(f184,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f47,f51])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.55    inference(flattening,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    spl3_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f32,f77])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    v1_relat_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.55    inference(flattening,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.55    inference(negated_conjecture,[],[f14])).
% 0.20/0.55  fof(f14,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f33,f72])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    v1_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    spl3_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f34,f67])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    spl3_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f35,f62])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ~spl3_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f36,f57])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ~r1_tarski(sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (25058)------------------------------
% 0.20/0.55  % (25058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25058)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (25058)Memory used [KB]: 8827
% 0.20/0.55  % (25058)Time elapsed: 0.137 s
% 0.20/0.55  % (25058)------------------------------
% 0.20/0.55  % (25058)------------------------------
% 0.20/0.55  % (25062)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (25036)Success in time 0.197 s
%------------------------------------------------------------------------------
