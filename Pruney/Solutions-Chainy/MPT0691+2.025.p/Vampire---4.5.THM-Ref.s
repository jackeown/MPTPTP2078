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
% DateTime   : Thu Dec  3 12:53:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 139 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  172 ( 279 expanded)
%              Number of equality atoms :   55 (  77 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f135,f216,f329,f424,f434])).

fof(f434,plain,
    ( k9_relat_1(sK1,sK0) != k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0))))
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f424,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f419,f213,f57,f421])).

fof(f421,plain,
    ( spl2_19
  <=> k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f57,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f213,plain,
    ( spl2_12
  <=> sK0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f419,plain,
    ( k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f401,f176])).

fof(f176,plain,
    ( ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0)
    | ~ spl2_3 ),
    inference(resolution,[],[f171,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(k7_relat_1(sK1,X1),X0) = k9_relat_1(sK1,X0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f34,f59])).

fof(f59,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f401,plain,
    ( k9_relat_1(k7_relat_1(sK1,sK0),sK0) = k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(superposition,[],[f378,f215])).

fof(f215,plain,
    ( sK0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f213])).

fof(f378,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f375,f104])).

fof(f104,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_3 ),
    inference(resolution,[],[f38,f59])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f375,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f77,f59])).

fof(f77,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f33,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f329,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f319,f213,f57,f326])).

fof(f326,plain,
    ( spl2_13
  <=> r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f319,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0))))
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(superposition,[],[f299,f215])).

fof(f299,plain,
    ( ! [X3] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X3),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X3))))
    | ~ spl2_3 ),
    inference(superposition,[],[f61,f293])).

fof(f293,plain,
    ( ! [X1] : k3_xboole_0(X1,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X1)))) = k3_xboole_0(k1_relat_1(sK1),X1)
    | ~ spl2_3 ),
    inference(superposition,[],[f290,f146])).

fof(f146,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))
    | ~ spl2_3 ),
    inference(resolution,[],[f43,f59])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f290,plain,
    ( ! [X0] : k3_xboole_0(k1_relat_1(sK1),X0) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f287,f104])).

fof(f287,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f67,f59])).

fof(f67,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f32,f37])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f216,plain,
    ( spl2_12
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f206,f132,f213])).

fof(f132,plain,
    ( spl2_10
  <=> k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f206,plain,
    ( sK0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_10 ),
    inference(superposition,[],[f202,f74])).

fof(f74,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f73,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f73,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f66,f31])).

fof(f31,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f32,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f202,plain,
    ( ! [X0] : k10_relat_1(k6_relat_1(sK0),X0) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(k6_relat_1(sK0),X0))
    | ~ spl2_10 ),
    inference(superposition,[],[f147,f134])).

fof(f134,plain,
    ( k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f147,plain,(
    ! [X4,X2,X3] : k10_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k3_xboole_0(X3,k10_relat_1(k6_relat_1(X2),X4)) ),
    inference(resolution,[],[f43,f29])).

fof(f135,plain,
    ( spl2_10
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f127,f52,f132])).

fof(f52,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f127,plain,
    ( k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f111,f54])).

fof(f54,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f111,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f109,f30])).

fof(f109,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f39,f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f60,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f55,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f28,f47])).

fof(f47,plain,
    ( spl2_1
  <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f28,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:39:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.52  % (22010)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (22018)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.53  % (22014)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.54  % (22004)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.55  % (22024)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.55  % (22012)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.55  % (22015)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.55  % (22019)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.56  % (22013)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.56  % (22016)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.56  % (22011)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.56  % (22008)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.57  % (22005)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.57  % (22007)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.57  % (22027)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.57  % (22006)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.58  % (22023)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.59  % (22019)Refutation found. Thanks to Tanya!
% 0.23/0.59  % SZS status Theorem for theBenchmark
% 0.23/0.59  % SZS output start Proof for theBenchmark
% 0.23/0.59  fof(f435,plain,(
% 0.23/0.59    $false),
% 0.23/0.59    inference(avatar_sat_refutation,[],[f50,f55,f60,f135,f216,f329,f424,f434])).
% 0.23/0.59  fof(f434,plain,(
% 0.23/0.59    k9_relat_1(sK1,sK0) != k2_relat_1(k7_relat_1(sK1,sK0)) | ~r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))) | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.23/0.59    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.59  fof(f424,plain,(
% 0.23/0.59    spl2_19 | ~spl2_3 | ~spl2_12),
% 0.23/0.59    inference(avatar_split_clause,[],[f419,f213,f57,f421])).
% 0.23/0.59  fof(f421,plain,(
% 0.23/0.59    spl2_19 <=> k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 0.23/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.23/0.59  fof(f57,plain,(
% 0.23/0.59    spl2_3 <=> v1_relat_1(sK1)),
% 0.23/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.59  fof(f213,plain,(
% 0.23/0.59    spl2_12 <=> sK0 = k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.23/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.23/0.59  fof(f419,plain,(
% 0.23/0.59    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_3 | ~spl2_12)),
% 0.23/0.59    inference(forward_demodulation,[],[f401,f176])).
% 0.23/0.59  fof(f176,plain,(
% 0.23/0.59    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0)) ) | ~spl2_3),
% 0.23/0.59    inference(resolution,[],[f171,f44])).
% 0.23/0.59  fof(f44,plain,(
% 0.23/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.59    inference(equality_resolution,[],[f41])).
% 0.23/0.59  fof(f41,plain,(
% 0.23/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.59    inference(cnf_transformation,[],[f2])).
% 0.23/0.59  fof(f2,axiom,(
% 0.23/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.59  fof(f171,plain,(
% 0.23/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k7_relat_1(sK1,X1),X0) = k9_relat_1(sK1,X0)) ) | ~spl2_3),
% 0.23/0.59    inference(resolution,[],[f34,f59])).
% 0.23/0.59  fof(f59,plain,(
% 0.23/0.59    v1_relat_1(sK1) | ~spl2_3),
% 0.23/0.59    inference(avatar_component_clause,[],[f57])).
% 0.23/0.59  fof(f34,plain,(
% 0.23/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f20])).
% 0.23/0.59  fof(f20,plain,(
% 0.23/0.59    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.23/0.59    inference(ennf_transformation,[],[f6])).
% 0.23/0.59  fof(f6,axiom,(
% 0.23/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.23/0.59  fof(f401,plain,(
% 0.23/0.59    k9_relat_1(k7_relat_1(sK1,sK0),sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_3 | ~spl2_12)),
% 0.23/0.59    inference(superposition,[],[f378,f215])).
% 0.23/0.59  fof(f215,plain,(
% 0.23/0.59    sK0 = k3_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_12),
% 0.23/0.59    inference(avatar_component_clause,[],[f213])).
% 0.23/0.59  fof(f378,plain,(
% 0.23/0.59    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0))) ) | ~spl2_3),
% 0.23/0.59    inference(forward_demodulation,[],[f375,f104])).
% 0.23/0.59  fof(f104,plain,(
% 0.23/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl2_3),
% 0.23/0.59    inference(resolution,[],[f38,f59])).
% 0.23/0.59  fof(f38,plain,(
% 0.23/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f22])).
% 0.23/0.59  fof(f22,plain,(
% 0.23/0.59    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.59    inference(ennf_transformation,[],[f9])).
% 0.23/0.59  fof(f9,axiom,(
% 0.23/0.59    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.23/0.59  fof(f375,plain,(
% 0.23/0.59    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_3),
% 0.23/0.59    inference(resolution,[],[f77,f59])).
% 0.23/0.59  fof(f77,plain,(
% 0.23/0.59    ( ! [X2,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))) )),
% 0.23/0.59    inference(resolution,[],[f33,f37])).
% 0.23/0.59  fof(f37,plain,(
% 0.23/0.59    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f21])).
% 0.23/0.59  fof(f21,plain,(
% 0.23/0.59    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.23/0.59    inference(ennf_transformation,[],[f4])).
% 0.23/0.59  fof(f4,axiom,(
% 0.23/0.59    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.23/0.59  fof(f33,plain,(
% 0.23/0.59    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f19])).
% 0.23/0.59  fof(f19,plain,(
% 0.23/0.59    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.59    inference(ennf_transformation,[],[f5])).
% 0.23/0.59  fof(f5,axiom,(
% 0.23/0.59    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.23/0.59  fof(f329,plain,(
% 0.23/0.59    spl2_13 | ~spl2_3 | ~spl2_12),
% 0.23/0.59    inference(avatar_split_clause,[],[f319,f213,f57,f326])).
% 0.23/0.59  fof(f326,plain,(
% 0.23/0.59    spl2_13 <=> r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0))))),
% 0.23/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.23/0.59  fof(f319,plain,(
% 0.23/0.59    r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))) | (~spl2_3 | ~spl2_12)),
% 0.23/0.59    inference(superposition,[],[f299,f215])).
% 0.23/0.59  fof(f299,plain,(
% 0.23/0.59    ( ! [X3] : (r1_tarski(k3_xboole_0(k1_relat_1(sK1),X3),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X3))))) ) | ~spl2_3),
% 0.23/0.59    inference(superposition,[],[f61,f293])).
% 0.23/0.59  fof(f293,plain,(
% 0.23/0.59    ( ! [X1] : (k3_xboole_0(X1,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X1)))) = k3_xboole_0(k1_relat_1(sK1),X1)) ) | ~spl2_3),
% 0.23/0.59    inference(superposition,[],[f290,f146])).
% 0.23/0.59  fof(f146,plain,(
% 0.23/0.59    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) ) | ~spl2_3),
% 0.23/0.59    inference(resolution,[],[f43,f59])).
% 0.23/0.59  fof(f43,plain,(
% 0.23/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 0.23/0.59    inference(cnf_transformation,[],[f25])).
% 0.23/0.59  fof(f25,plain,(
% 0.23/0.59    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.23/0.59    inference(ennf_transformation,[],[f12])).
% 0.23/0.59  fof(f12,axiom,(
% 0.23/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.23/0.59  fof(f290,plain,(
% 0.23/0.59    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK1),X0) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_3),
% 0.23/0.59    inference(forward_demodulation,[],[f287,f104])).
% 0.23/0.59  fof(f287,plain,(
% 0.23/0.59    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_3),
% 0.23/0.59    inference(resolution,[],[f67,f59])).
% 0.23/0.59  fof(f67,plain,(
% 0.23/0.59    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))) )),
% 0.23/0.59    inference(resolution,[],[f32,f37])).
% 0.23/0.59  fof(f32,plain,(
% 0.23/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 0.23/0.59    inference(cnf_transformation,[],[f18])).
% 0.23/0.59  fof(f18,plain,(
% 0.23/0.59    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.23/0.59    inference(ennf_transformation,[],[f7])).
% 0.23/0.59  fof(f7,axiom,(
% 0.23/0.59    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.23/0.59  fof(f61,plain,(
% 0.23/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.23/0.59    inference(superposition,[],[f35,f36])).
% 0.23/0.59  fof(f36,plain,(
% 0.23/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f1])).
% 0.23/0.59  fof(f1,axiom,(
% 0.23/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.59  fof(f35,plain,(
% 0.23/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f3])).
% 0.23/0.59  fof(f3,axiom,(
% 0.23/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.23/0.59  fof(f216,plain,(
% 0.23/0.59    spl2_12 | ~spl2_10),
% 0.23/0.59    inference(avatar_split_clause,[],[f206,f132,f213])).
% 0.23/0.59  fof(f132,plain,(
% 0.23/0.59    spl2_10 <=> k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 0.23/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.23/0.59  fof(f206,plain,(
% 0.23/0.59    sK0 = k3_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_10),
% 0.23/0.59    inference(superposition,[],[f202,f74])).
% 0.23/0.59  fof(f74,plain,(
% 0.23/0.59    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.23/0.59    inference(forward_demodulation,[],[f73,f30])).
% 0.23/0.59  fof(f30,plain,(
% 0.23/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.59    inference(cnf_transformation,[],[f8])).
% 0.23/0.59  fof(f8,axiom,(
% 0.23/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.23/0.59  fof(f73,plain,(
% 0.23/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 0.23/0.59    inference(forward_demodulation,[],[f66,f31])).
% 0.23/0.59  fof(f31,plain,(
% 0.23/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.59    inference(cnf_transformation,[],[f8])).
% 0.23/0.59  fof(f66,plain,(
% 0.23/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 0.23/0.59    inference(resolution,[],[f32,f29])).
% 0.23/0.59  fof(f29,plain,(
% 0.23/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.59    inference(cnf_transformation,[],[f15])).
% 0.23/0.59  fof(f15,plain,(
% 0.23/0.59    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.23/0.59    inference(pure_predicate_removal,[],[f11])).
% 0.23/0.59  fof(f11,axiom,(
% 0.23/0.59    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.23/0.59  fof(f202,plain,(
% 0.23/0.59    ( ! [X0] : (k10_relat_1(k6_relat_1(sK0),X0) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(k6_relat_1(sK0),X0))) ) | ~spl2_10),
% 0.23/0.59    inference(superposition,[],[f147,f134])).
% 0.23/0.59  fof(f134,plain,(
% 0.23/0.59    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_10),
% 0.23/0.59    inference(avatar_component_clause,[],[f132])).
% 0.23/0.59  fof(f147,plain,(
% 0.23/0.59    ( ! [X4,X2,X3] : (k10_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k3_xboole_0(X3,k10_relat_1(k6_relat_1(X2),X4))) )),
% 0.23/0.59    inference(resolution,[],[f43,f29])).
% 0.23/0.59  fof(f135,plain,(
% 0.23/0.59    spl2_10 | ~spl2_2),
% 0.23/0.59    inference(avatar_split_clause,[],[f127,f52,f132])).
% 0.23/0.59  fof(f52,plain,(
% 0.23/0.59    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.23/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.59  fof(f127,plain,(
% 0.23/0.59    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_2),
% 0.23/0.59    inference(resolution,[],[f111,f54])).
% 0.23/0.59  fof(f54,plain,(
% 0.23/0.59    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 0.23/0.59    inference(avatar_component_clause,[],[f52])).
% 0.23/0.59  fof(f111,plain,(
% 0.23/0.59    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 0.23/0.59    inference(forward_demodulation,[],[f109,f30])).
% 0.23/0.59  fof(f109,plain,(
% 0.23/0.59    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 0.23/0.59    inference(resolution,[],[f39,f29])).
% 0.23/0.59  fof(f39,plain,(
% 0.23/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.23/0.59    inference(cnf_transformation,[],[f24])).
% 0.23/0.59  fof(f24,plain,(
% 0.23/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.59    inference(flattening,[],[f23])).
% 0.23/0.59  fof(f23,plain,(
% 0.23/0.59    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.59    inference(ennf_transformation,[],[f10])).
% 0.23/0.59  fof(f10,axiom,(
% 0.23/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.23/0.59  fof(f60,plain,(
% 0.23/0.59    spl2_3),
% 0.23/0.59    inference(avatar_split_clause,[],[f26,f57])).
% 0.23/0.59  fof(f26,plain,(
% 0.23/0.59    v1_relat_1(sK1)),
% 0.23/0.59    inference(cnf_transformation,[],[f17])).
% 0.23/0.59  fof(f17,plain,(
% 0.23/0.59    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.23/0.59    inference(flattening,[],[f16])).
% 0.23/0.59  fof(f16,plain,(
% 0.23/0.59    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.23/0.59    inference(ennf_transformation,[],[f14])).
% 0.23/0.59  fof(f14,negated_conjecture,(
% 0.23/0.59    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.23/0.59    inference(negated_conjecture,[],[f13])).
% 0.23/0.59  fof(f13,conjecture,(
% 0.23/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.23/0.59  fof(f55,plain,(
% 0.23/0.59    spl2_2),
% 0.23/0.59    inference(avatar_split_clause,[],[f27,f52])).
% 0.23/0.59  fof(f27,plain,(
% 0.23/0.59    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.23/0.59    inference(cnf_transformation,[],[f17])).
% 0.23/0.59  fof(f50,plain,(
% 0.23/0.59    ~spl2_1),
% 0.23/0.59    inference(avatar_split_clause,[],[f28,f47])).
% 0.23/0.59  fof(f47,plain,(
% 0.23/0.59    spl2_1 <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.23/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.59  fof(f28,plain,(
% 0.23/0.59    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.23/0.59    inference(cnf_transformation,[],[f17])).
% 0.23/0.59  % SZS output end Proof for theBenchmark
% 0.23/0.59  % (22019)------------------------------
% 0.23/0.59  % (22019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.59  % (22019)Termination reason: Refutation
% 0.23/0.59  
% 0.23/0.59  % (22019)Memory used [KB]: 6524
% 0.23/0.59  % (22019)Time elapsed: 0.103 s
% 0.23/0.59  % (22019)------------------------------
% 0.23/0.59  % (22019)------------------------------
% 0.23/0.60  % (22003)Success in time 0.229 s
%------------------------------------------------------------------------------
