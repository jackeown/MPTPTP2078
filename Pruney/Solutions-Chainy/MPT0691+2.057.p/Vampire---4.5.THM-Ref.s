%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:52 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 128 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  200 ( 302 expanded)
%              Number of equality atoms :   31 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1595,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f106,f128,f143,f147,f1592])).

fof(f1592,plain,
    ( ~ spl2_1
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f1591])).

fof(f1591,plain,
    ( $false
    | ~ spl2_1
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f1573,f127])).

fof(f127,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1573,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f598,f146])).

fof(f146,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl2_5
  <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f598,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f303,f124])).

fof(f124,plain,
    ( ! [X2] : k1_relat_1(k7_relat_1(sK1,X2)) = k10_relat_1(k7_relat_1(sK1,X2),k9_relat_1(sK1,X2))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f113,f93])).

fof(f93,plain,
    ( ! [X1] : k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1)
    | ~ spl2_1 ),
    inference(resolution,[],[f89,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f89,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f113,plain,
    ( ! [X2] : k10_relat_1(k7_relat_1(sK1,X2),k2_relat_1(k7_relat_1(sK1,X2))) = k1_relat_1(k7_relat_1(sK1,X2))
    | ~ spl2_1 ),
    inference(resolution,[],[f100,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f100,plain,
    ( ! [X9] : v1_relat_1(k7_relat_1(sK1,X9))
    | ~ spl2_1 ),
    inference(resolution,[],[f89,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f303,plain,
    ( ! [X6,X5] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X5),X6),k10_relat_1(sK1,X6))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f302,f225])).

fof(f225,plain,
    ( ! [X3] : k7_relat_1(sK1,X3) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X3)))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f221,f120])).

fof(f120,plain,
    ( ! [X17] : k7_relat_1(sK1,X17) = k7_relat_1(k7_relat_1(sK1,X17),k1_relat_1(k7_relat_1(sK1,X17)))
    | ~ spl2_1 ),
    inference(resolution,[],[f100,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f221,plain,
    ( ! [X3] : k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X3))) = k7_relat_1(k7_relat_1(sK1,X3),k1_relat_1(k7_relat_1(sK1,X3)))
    | ~ spl2_1 ),
    inference(resolution,[],[f94,f97])).

fof(f97,plain,
    ( ! [X7] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X7)),X7)
    | ~ spl2_1 ),
    inference(resolution,[],[f89,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f94,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k7_relat_1(k7_relat_1(sK1,X3),X2) = k7_relat_1(sK1,X2) )
    | ~ spl2_1 ),
    inference(resolution,[],[f89,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f302,plain,
    ( ! [X6,X5] : r1_tarski(k10_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))),X6),k10_relat_1(sK1,X6))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f301,f100])).

fof(f301,plain,
    ( ! [X6,X5] :
        ( ~ v1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))))
        | r1_tarski(k10_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))),X6),k10_relat_1(sK1,X6)) )
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f293,f89])).

fof(f293,plain,
    ( ! [X6,X5] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))))
        | r1_tarski(k10_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))),X6),k10_relat_1(sK1,X6)) )
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f213,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

fof(f213,plain,
    ( ! [X5] : r1_tarski(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))),sK1)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f210,f142])).

fof(f142,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl2_4
  <=> sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f210,plain,
    ( ! [X5] : r1_tarski(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))),k7_relat_1(sK1,k1_relat_1(sK1)))
    | ~ spl2_1 ),
    inference(resolution,[],[f95,f96])).

fof(f96,plain,
    ( ! [X6] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X6)),k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f89,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(f95,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X4,X5)
        | r1_tarski(k7_relat_1(sK1,X4),k7_relat_1(sK1,X5)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f89,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

fof(f147,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f111,f104,f88,f145])).

fof(f104,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f111,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f107,f89])).

fof(f107,plain,
    ( ~ v1_relat_1(sK1)
    | sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f105,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f105,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f143,plain,
    ( spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f99,f88,f141])).

fof(f99,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f89,f75])).

fof(f128,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f59,f126])).

fof(f59,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f106,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f58,f104])).

fof(f58,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f57,f88])).

fof(f57,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:24:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.48  % (20131)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (20139)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.50  % (20147)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.51  % (20130)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.51  % (20134)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.51  % (20125)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.51  % (20151)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (20138)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.52  % (20148)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.52  % (20129)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.52  % (20127)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.52  % (20126)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.52  % (20140)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.52  % (20152)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.52  % (20128)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.53  % (20154)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.53  % (20141)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.53  % (20146)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.53  % (20143)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.53  % (20153)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.53  % (20133)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.53  % (20145)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.53  % (20144)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.54  % (20132)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.54  % (20150)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.54  % (20136)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.54  % (20137)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.54  % (20135)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.54  % (20142)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.54  % (20149)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.66/0.62  % (20151)Refutation found. Thanks to Tanya!
% 1.66/0.62  % SZS status Theorem for theBenchmark
% 1.66/0.62  % SZS output start Proof for theBenchmark
% 1.66/0.62  fof(f1595,plain,(
% 1.66/0.62    $false),
% 1.66/0.62    inference(avatar_sat_refutation,[],[f90,f106,f128,f143,f147,f1592])).
% 1.66/0.62  fof(f1592,plain,(
% 1.66/0.62    ~spl2_1 | spl2_3 | ~spl2_4 | ~spl2_5),
% 1.66/0.62    inference(avatar_contradiction_clause,[],[f1591])).
% 1.66/0.62  fof(f1591,plain,(
% 1.66/0.62    $false | (~spl2_1 | spl2_3 | ~spl2_4 | ~spl2_5)),
% 1.66/0.62    inference(subsumption_resolution,[],[f1573,f127])).
% 1.66/0.62  fof(f127,plain,(
% 1.66/0.62    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | spl2_3),
% 1.66/0.62    inference(avatar_component_clause,[],[f126])).
% 1.66/0.62  fof(f126,plain,(
% 1.66/0.62    spl2_3 <=> r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.66/0.62  fof(f1573,plain,(
% 1.66/0.62    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | (~spl2_1 | ~spl2_4 | ~spl2_5)),
% 1.66/0.62    inference(superposition,[],[f598,f146])).
% 1.66/0.62  fof(f146,plain,(
% 1.66/0.62    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_5),
% 1.66/0.62    inference(avatar_component_clause,[],[f145])).
% 1.66/0.62  fof(f145,plain,(
% 1.66/0.62    spl2_5 <=> sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.66/0.62  fof(f598,plain,(
% 1.66/0.62    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | (~spl2_1 | ~spl2_4)),
% 1.66/0.62    inference(superposition,[],[f303,f124])).
% 1.66/0.62  fof(f124,plain,(
% 1.66/0.62    ( ! [X2] : (k1_relat_1(k7_relat_1(sK1,X2)) = k10_relat_1(k7_relat_1(sK1,X2),k9_relat_1(sK1,X2))) ) | ~spl2_1),
% 1.66/0.62    inference(forward_demodulation,[],[f113,f93])).
% 1.66/0.62  fof(f93,plain,(
% 1.66/0.62    ( ! [X1] : (k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1)) ) | ~spl2_1),
% 1.66/0.62    inference(resolution,[],[f89,f63])).
% 1.66/0.62  fof(f63,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f39])).
% 1.66/0.62  fof(f39,plain,(
% 1.66/0.62    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f16])).
% 1.66/0.62  fof(f16,axiom,(
% 1.66/0.62    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.66/0.62  fof(f89,plain,(
% 1.66/0.62    v1_relat_1(sK1) | ~spl2_1),
% 1.66/0.62    inference(avatar_component_clause,[],[f88])).
% 1.66/0.62  fof(f88,plain,(
% 1.66/0.62    spl2_1 <=> v1_relat_1(sK1)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.66/0.62  fof(f113,plain,(
% 1.66/0.62    ( ! [X2] : (k10_relat_1(k7_relat_1(sK1,X2),k2_relat_1(k7_relat_1(sK1,X2))) = k1_relat_1(k7_relat_1(sK1,X2))) ) | ~spl2_1),
% 1.66/0.62    inference(resolution,[],[f100,f62])).
% 1.66/0.62  fof(f62,plain,(
% 1.66/0.62    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f38])).
% 1.66/0.62  fof(f38,plain,(
% 1.66/0.62    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f18])).
% 1.66/0.62  fof(f18,axiom,(
% 1.66/0.62    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.66/0.62  fof(f100,plain,(
% 1.66/0.62    ( ! [X9] : (v1_relat_1(k7_relat_1(sK1,X9))) ) | ~spl2_1),
% 1.66/0.62    inference(resolution,[],[f89,f76])).
% 1.66/0.62  fof(f76,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f54])).
% 1.66/0.62  fof(f54,plain,(
% 1.66/0.62    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f13])).
% 1.66/0.62  fof(f13,axiom,(
% 1.66/0.62    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.66/0.62  fof(f303,plain,(
% 1.66/0.62    ( ! [X6,X5] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X5),X6),k10_relat_1(sK1,X6))) ) | (~spl2_1 | ~spl2_4)),
% 1.66/0.62    inference(forward_demodulation,[],[f302,f225])).
% 1.66/0.62  fof(f225,plain,(
% 1.66/0.62    ( ! [X3] : (k7_relat_1(sK1,X3) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X3)))) ) | ~spl2_1),
% 1.66/0.62    inference(forward_demodulation,[],[f221,f120])).
% 1.66/0.62  fof(f120,plain,(
% 1.66/0.62    ( ! [X17] : (k7_relat_1(sK1,X17) = k7_relat_1(k7_relat_1(sK1,X17),k1_relat_1(k7_relat_1(sK1,X17)))) ) | ~spl2_1),
% 1.66/0.62    inference(resolution,[],[f100,f75])).
% 1.66/0.62  fof(f75,plain,(
% 1.66/0.62    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 1.66/0.62    inference(cnf_transformation,[],[f53])).
% 1.66/0.62  fof(f53,plain,(
% 1.66/0.62    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f28])).
% 1.66/0.62  fof(f28,axiom,(
% 1.66/0.62    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 1.66/0.62  fof(f221,plain,(
% 1.66/0.62    ( ! [X3] : (k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X3))) = k7_relat_1(k7_relat_1(sK1,X3),k1_relat_1(k7_relat_1(sK1,X3)))) ) | ~spl2_1),
% 1.66/0.62    inference(resolution,[],[f94,f97])).
% 1.66/0.62  fof(f97,plain,(
% 1.66/0.62    ( ! [X7] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X7)),X7)) ) | ~spl2_1),
% 1.66/0.62    inference(resolution,[],[f89,f73])).
% 1.66/0.62  fof(f73,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f51])).
% 1.66/0.62  fof(f51,plain,(
% 1.66/0.62    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f24])).
% 1.66/0.62  fof(f24,axiom,(
% 1.66/0.62    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.66/0.62  fof(f94,plain,(
% 1.66/0.62    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k7_relat_1(k7_relat_1(sK1,X3),X2) = k7_relat_1(sK1,X2)) ) | ~spl2_1),
% 1.66/0.62    inference(resolution,[],[f89,f65])).
% 1.66/0.62  fof(f65,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f43])).
% 1.66/0.62  fof(f43,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.66/0.62    inference(flattening,[],[f42])).
% 1.66/0.62  fof(f42,plain,(
% 1.66/0.62    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.66/0.62    inference(ennf_transformation,[],[f14])).
% 1.66/0.62  fof(f14,axiom,(
% 1.66/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).
% 1.66/0.62  fof(f302,plain,(
% 1.66/0.62    ( ! [X6,X5] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))),X6),k10_relat_1(sK1,X6))) ) | (~spl2_1 | ~spl2_4)),
% 1.66/0.62    inference(subsumption_resolution,[],[f301,f100])).
% 1.66/0.62  fof(f301,plain,(
% 1.66/0.62    ( ! [X6,X5] : (~v1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5)))) | r1_tarski(k10_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))),X6),k10_relat_1(sK1,X6))) ) | (~spl2_1 | ~spl2_4)),
% 1.66/0.62    inference(subsumption_resolution,[],[f293,f89])).
% 1.66/0.62  fof(f293,plain,(
% 1.66/0.62    ( ! [X6,X5] : (~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5)))) | r1_tarski(k10_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))),X6),k10_relat_1(sK1,X6))) ) | (~spl2_1 | ~spl2_4)),
% 1.66/0.62    inference(resolution,[],[f213,f60])).
% 1.66/0.62  fof(f60,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f36])).
% 1.66/0.62  fof(f36,plain,(
% 1.66/0.62    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.66/0.62    inference(flattening,[],[f35])).
% 1.66/0.62  fof(f35,plain,(
% 1.66/0.62    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f19])).
% 1.66/0.62  fof(f19,axiom,(
% 1.66/0.62    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).
% 1.66/0.62  fof(f213,plain,(
% 1.66/0.62    ( ! [X5] : (r1_tarski(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))),sK1)) ) | (~spl2_1 | ~spl2_4)),
% 1.66/0.62    inference(forward_demodulation,[],[f210,f142])).
% 1.66/0.62  fof(f142,plain,(
% 1.66/0.62    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) | ~spl2_4),
% 1.66/0.62    inference(avatar_component_clause,[],[f141])).
% 1.66/0.62  fof(f141,plain,(
% 1.66/0.62    spl2_4 <=> sK1 = k7_relat_1(sK1,k1_relat_1(sK1))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.66/0.62  fof(f210,plain,(
% 1.66/0.62    ( ! [X5] : (r1_tarski(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X5))),k7_relat_1(sK1,k1_relat_1(sK1)))) ) | ~spl2_1),
% 1.66/0.62    inference(resolution,[],[f95,f96])).
% 1.66/0.62  fof(f96,plain,(
% 1.66/0.62    ( ! [X6] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X6)),k1_relat_1(sK1))) ) | ~spl2_1),
% 1.66/0.62    inference(resolution,[],[f89,f72])).
% 1.66/0.62  fof(f72,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f50])).
% 1.66/0.62  fof(f50,plain,(
% 1.66/0.62    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f25])).
% 1.66/0.62  fof(f25,axiom,(
% 1.66/0.62    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
% 1.66/0.62  fof(f95,plain,(
% 1.66/0.62    ( ! [X4,X5] : (~r1_tarski(X4,X5) | r1_tarski(k7_relat_1(sK1,X4),k7_relat_1(sK1,X5))) ) | ~spl2_1),
% 1.66/0.62    inference(resolution,[],[f89,f66])).
% 1.66/0.62  fof(f66,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f45])).
% 1.66/0.62  fof(f45,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.66/0.62    inference(flattening,[],[f44])).
% 1.66/0.62  fof(f44,plain,(
% 1.66/0.62    ! [X0,X1,X2] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.66/0.62    inference(ennf_transformation,[],[f15])).
% 1.66/0.62  fof(f15,axiom,(
% 1.66/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).
% 1.66/0.62  fof(f147,plain,(
% 1.66/0.62    spl2_5 | ~spl2_1 | ~spl2_2),
% 1.66/0.62    inference(avatar_split_clause,[],[f111,f104,f88,f145])).
% 1.66/0.62  fof(f104,plain,(
% 1.66/0.62    spl2_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.66/0.62  fof(f111,plain,(
% 1.66/0.62    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_2)),
% 1.66/0.62    inference(subsumption_resolution,[],[f107,f89])).
% 1.66/0.62  fof(f107,plain,(
% 1.66/0.62    ~v1_relat_1(sK1) | sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_2),
% 1.66/0.62    inference(resolution,[],[f105,f71])).
% 1.66/0.62  fof(f71,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.66/0.62    inference(cnf_transformation,[],[f49])).
% 1.66/0.62  fof(f49,plain,(
% 1.66/0.62    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.66/0.62    inference(flattening,[],[f48])).
% 1.66/0.62  fof(f48,plain,(
% 1.66/0.62    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f26])).
% 1.66/0.62  fof(f26,axiom,(
% 1.66/0.62    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.66/0.62  fof(f105,plain,(
% 1.66/0.62    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_2),
% 1.66/0.62    inference(avatar_component_clause,[],[f104])).
% 1.66/0.62  fof(f143,plain,(
% 1.66/0.62    spl2_4 | ~spl2_1),
% 1.66/0.62    inference(avatar_split_clause,[],[f99,f88,f141])).
% 1.66/0.62  fof(f99,plain,(
% 1.66/0.62    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) | ~spl2_1),
% 1.66/0.62    inference(resolution,[],[f89,f75])).
% 1.66/0.62  fof(f128,plain,(
% 1.66/0.62    ~spl2_3),
% 1.66/0.62    inference(avatar_split_clause,[],[f59,f126])).
% 1.66/0.62  fof(f59,plain,(
% 1.66/0.62    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.66/0.62    inference(cnf_transformation,[],[f34])).
% 1.66/0.62  fof(f34,plain,(
% 1.66/0.62    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.66/0.62    inference(flattening,[],[f33])).
% 1.66/0.62  fof(f33,plain,(
% 1.66/0.62    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f31])).
% 1.66/0.62  fof(f31,negated_conjecture,(
% 1.66/0.62    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.66/0.62    inference(negated_conjecture,[],[f30])).
% 1.66/0.62  fof(f30,conjecture,(
% 1.66/0.62    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.66/0.62  fof(f106,plain,(
% 1.66/0.62    spl2_2),
% 1.66/0.62    inference(avatar_split_clause,[],[f58,f104])).
% 1.66/0.62  fof(f58,plain,(
% 1.66/0.62    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.66/0.62    inference(cnf_transformation,[],[f34])).
% 1.66/0.62  fof(f90,plain,(
% 1.66/0.62    spl2_1),
% 1.66/0.62    inference(avatar_split_clause,[],[f57,f88])).
% 1.66/0.62  fof(f57,plain,(
% 1.66/0.62    v1_relat_1(sK1)),
% 1.66/0.62    inference(cnf_transformation,[],[f34])).
% 1.66/0.62  % SZS output end Proof for theBenchmark
% 1.66/0.62  % (20151)------------------------------
% 1.66/0.62  % (20151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (20151)Termination reason: Refutation
% 1.66/0.62  
% 1.66/0.62  % (20151)Memory used [KB]: 7291
% 1.66/0.62  % (20151)Time elapsed: 0.184 s
% 1.66/0.62  % (20151)------------------------------
% 1.66/0.62  % (20151)------------------------------
% 1.66/0.62  % (20124)Success in time 0.272 s
%------------------------------------------------------------------------------
