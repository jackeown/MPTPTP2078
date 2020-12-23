%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 202 expanded)
%              Number of leaves         :   15 (  53 expanded)
%              Depth                    :   17
%              Number of atoms          :  279 ( 850 expanded)
%              Number of equality atoms :   73 ( 289 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f81,f85,f97,f150])).

fof(f150,plain,
    ( spl1_2
    | ~ spl1_3 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f148,f27])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f148,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f147,f28])).

fof(f28,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f147,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f146,f29])).

fof(f29,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f146,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f144,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f144,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f143,f27])).

fof(f143,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f142,f28])).

fof(f142,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f137,f29])).

fof(f137,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f118,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f61,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f61,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f35,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f118,plain,
    ( k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f117,f27])).

fof(f117,plain,
    ( k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f116,f75])).

fof(f75,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl1_3
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f116,plain,
    ( k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_2 ),
    inference(superposition,[],[f55,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f55,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f97,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl1_4 ),
    inference(subsumption_resolution,[],[f95,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f95,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | spl1_4 ),
    inference(subsumption_resolution,[],[f92,f27])).

fof(f92,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | spl1_4 ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | spl1_4 ),
    inference(superposition,[],[f89,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f70,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f69,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f37,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f89,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
    | spl1_4 ),
    inference(subsumption_resolution,[],[f88,f27])).

fof(f88,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(subsumption_resolution,[],[f87,f28])).

fof(f87,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f86,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(superposition,[],[f80,f40])).

fof(f80,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k2_funct_1(sK0)))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl1_4
  <=> k1_relat_1(sK0) = k10_relat_1(sK0,k1_relat_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f85,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f83,f27])).

fof(f83,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f82,f28])).

fof(f82,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f76,f38])).

fof(f76,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f81,plain,
    ( ~ spl1_3
    | ~ spl1_4
    | spl1_1 ),
    inference(avatar_split_clause,[],[f72,f49,f78,f74])).

fof(f49,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f72,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(subsumption_resolution,[],[f67,f27])).

fof(f67,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(superposition,[],[f51,f37])).

fof(f51,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f56,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f30,f53,f49])).

fof(f30,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:00:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (30232)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (30240)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (30231)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (30230)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (30239)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (30231)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f56,f81,f85,f97,f150])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    spl1_2 | ~spl1_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f149])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    $false | (spl1_2 | ~spl1_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f148,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    v1_relat_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f10])).
% 0.22/0.51  fof(f10,conjecture,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f147,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    v1_funct_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f146,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    v2_funct_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f145])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k1_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.22/0.51    inference(superposition,[],[f144,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | (spl1_2 | ~spl1_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f143,f27])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f142,f28])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f137,f29])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.22/0.51    inference(superposition,[],[f118,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f61,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k2_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(superposition,[],[f35,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | (spl1_2 | ~spl1_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f117,f27])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f116,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    v1_relat_1(k2_funct_1(sK0)) | ~spl1_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    spl1_3 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | spl1_2),
% 0.22/0.51    inference(superposition,[],[f55,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl1_2 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl1_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f96])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    $false | spl1_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f95,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | spl1_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f92,f27])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ~v1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | spl1_4),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k1_relat_1(sK0) | ~v1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | spl1_4),
% 0.22/0.51    inference(superposition,[],[f89,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f70,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f69,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(superposition,[],[f37,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) | spl1_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f88,f27])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f87,f28])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f86,f29])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_4),
% 0.22/0.51    inference(superposition,[],[f80,f40])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k2_funct_1(sK0))) | spl1_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    spl1_4 <=> k1_relat_1(sK0) = k10_relat_1(sK0,k1_relat_1(k2_funct_1(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl1_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    $false | spl1_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f83,f27])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ~v1_relat_1(sK0) | spl1_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f82,f28])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 0.22/0.51    inference(resolution,[],[f76,f38])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ~v1_relat_1(k2_funct_1(sK0)) | spl1_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f74])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ~spl1_3 | ~spl1_4 | spl1_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f72,f49,f78,f74])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    spl1_1 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | spl1_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f67,f27])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | spl1_1),
% 0.22/0.51    inference(superposition,[],[f51,f37])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f49])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ~spl1_1 | ~spl1_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f30,f53,f49])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (30231)------------------------------
% 0.22/0.51  % (30231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30231)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (30231)Memory used [KB]: 6140
% 0.22/0.51  % (30231)Time elapsed: 0.112 s
% 0.22/0.51  % (30231)------------------------------
% 0.22/0.51  % (30231)------------------------------
% 0.22/0.51  % (30226)Success in time 0.151 s
%------------------------------------------------------------------------------
