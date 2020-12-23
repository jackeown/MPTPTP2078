%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 229 expanded)
%              Number of leaves         :   19 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  360 ( 934 expanded)
%              Number of equality atoms :  109 ( 328 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f124,f128,f150,f249,f255,f265])).

fof(f265,plain,(
    spl1_8 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl1_8 ),
    inference(subsumption_resolution,[],[f263,f33])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f29])).

fof(f29,plain,
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

fof(f15,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f263,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_8 ),
    inference(subsumption_resolution,[],[f262,f34])).

fof(f34,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f262,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_8 ),
    inference(subsumption_resolution,[],[f261,f35])).

fof(f35,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f261,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_8 ),
    inference(trivial_inequality_removal,[],[f260])).

fof(f260,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_8 ),
    inference(superposition,[],[f248,f47])).

fof(f47,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f248,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | spl1_8 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl1_8
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f255,plain,(
    spl1_7 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl1_7 ),
    inference(subsumption_resolution,[],[f253,f33])).

fof(f253,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_7 ),
    inference(subsumption_resolution,[],[f252,f34])).

fof(f252,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_7 ),
    inference(subsumption_resolution,[],[f251,f35])).

fof(f251,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_7 ),
    inference(trivial_inequality_removal,[],[f250])).

fof(f250,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_7 ),
    inference(superposition,[],[f244,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f244,plain,
    ( k1_relat_1(k2_funct_1(sK0)) != k2_relat_1(sK0)
    | spl1_7 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl1_7
  <=> k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f249,plain,
    ( ~ spl1_7
    | ~ spl1_8
    | spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f240,f116,f61,f246,f242])).

fof(f61,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f116,plain,
    ( spl1_3
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f240,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | k1_relat_1(k2_funct_1(sK0)) != k2_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f239,f117])).

fof(f117,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f239,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | k1_relat_1(k2_funct_1(sK0)) != k2_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f238,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f238,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),X0)
        | k2_relat_1(sK0) != X0 )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f237,f117])).

fof(f237,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),X0)
        | k2_relat_1(sK0) != X0
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f234,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f234,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0))
        | k2_relat_1(sK0) != X0 )
    | spl1_2
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f233,f40])).

fof(f40,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f233,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0))
        | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0) )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f232,f117])).

fof(f232,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0))
        | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f227,f37])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f227,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0))
        | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f224,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f224,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
        | k2_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f223,f33])).

fof(f223,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
        | k2_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0) )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f207,f117])).

fof(f207,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
        | k2_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0) )
    | spl1_2 ),
    inference(superposition,[],[f63,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(f63,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f150,plain,(
    ~ spl1_4 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f148,f33])).

fof(f148,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f147,f34])).

fof(f147,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f146,f35])).

fof(f146,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f145,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f145,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(superposition,[],[f141,f46])).

fof(f141,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0)))
    | ~ spl1_4 ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,
    ( ! [X0] :
        ( k1_relat_1(k2_funct_1(sK0)) != X0
        | ~ r1_tarski(k2_relat_1(sK0),X0) )
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f136,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f136,plain,
    ( ! [X0] :
        ( k1_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(sK0))
        | ~ r1_tarski(k2_relat_1(sK0),X0) )
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f135,f33])).

fof(f135,plain,
    ( ! [X0] :
        ( k1_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(sK0))
        | ~ r1_tarski(k2_relat_1(sK0),X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f134,f37])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k6_relat_1(X0))
        | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(sK0))
        | ~ r1_tarski(k2_relat_1(sK0),X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl1_4 ),
    inference(trivial_inequality_removal,[],[f129])).

fof(f129,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k1_relat_1(sK0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(sK0))
        | ~ r1_tarski(k2_relat_1(sK0),X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl1_4 ),
    inference(superposition,[],[f121,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f121,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X0))
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k1_relat_1(k2_funct_1(sK0)) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl1_4
  <=> ! [X0] :
        ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X0))
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k1_relat_1(k2_funct_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f128,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f126,f33])).

fof(f126,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f125,f34])).

fof(f125,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f118,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f118,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f124,plain,
    ( ~ spl1_3
    | spl1_4
    | spl1_1 ),
    inference(avatar_split_clause,[],[f123,f57,f120,f116])).

fof(f57,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f123,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X0))
        | k1_relat_1(X0) != k1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_1 ),
    inference(subsumption_resolution,[],[f98,f33])).

fof(f98,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X0))
        | k1_relat_1(X0) != k1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_1 ),
    inference(superposition,[],[f59,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(f59,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f64,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f36,f61,f57])).

fof(f36,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:00:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (29187)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (29197)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (29195)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (29190)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (29184)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (29189)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (29196)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (29201)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (29202)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (29185)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (29203)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (29188)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (29186)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (29192)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (29204)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (29193)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (29205)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (29200)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (29186)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (29194)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (29182)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f64,f124,f128,f150,f249,f255,f265])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    spl1_8),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f264])).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    $false | spl1_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f263,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    v1_relat_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.21/0.54  fof(f263,plain,(
% 0.21/0.54    ~v1_relat_1(sK0) | spl1_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f262,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v1_funct_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f262,plain,(
% 0.21/0.54    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f261,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    v2_funct_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f261,plain,(
% 0.21/0.54    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_8),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f260])).
% 0.21/0.54  fof(f260,plain,(
% 0.21/0.54    k1_relat_1(sK0) != k1_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_8),
% 0.21/0.54    inference(superposition,[],[f248,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | spl1_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f246])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    spl1_8 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    spl1_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f254])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    $false | spl1_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f253,f33])).
% 0.21/0.54  fof(f253,plain,(
% 0.21/0.54    ~v1_relat_1(sK0) | spl1_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f252,f34])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f251,f35])).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_7),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f250])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    k2_relat_1(sK0) != k2_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_7),
% 0.21/0.54    inference(superposition,[],[f244,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    k1_relat_1(k2_funct_1(sK0)) != k2_relat_1(sK0) | spl1_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f242])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    spl1_7 <=> k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    ~spl1_7 | ~spl1_8 | spl1_2 | ~spl1_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f240,f116,f61,f246,f242])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    spl1_2 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl1_3 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | k1_relat_1(k2_funct_1(sK0)) != k2_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f239,f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    v1_relat_1(k2_funct_1(sK0)) | ~spl1_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f116])).
% 0.21/0.54  fof(f239,plain,(
% 0.21/0.54    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | k1_relat_1(k2_funct_1(sK0)) != k2_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | (spl1_2 | ~spl1_3)),
% 0.21/0.54    inference(superposition,[],[f238,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),X0) | k2_relat_1(sK0) != X0) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f237,f117])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),X0) | k2_relat_1(sK0) != X0 | ~v1_relat_1(k2_funct_1(sK0))) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.54    inference(superposition,[],[f234,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) | k2_relat_1(sK0) != X0) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.54    inference(forward_demodulation,[],[f233,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0)) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f232,f117])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0))) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f227,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.54  fof(f227,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k2_funct_1(sK0))) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.54    inference(superposition,[],[f224,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(X0)) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f223,f33])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f207,f117])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) ) | spl1_2),
% 0.21/0.54    inference(superposition,[],[f63,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f61])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ~spl1_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    $false | ~spl1_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f148,f33])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f147,f34])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f146,f35])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f145,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.54    inference(superposition,[],[f141,f46])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0))) | ~spl1_4),
% 0.21/0.54    inference(equality_resolution,[],[f137])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(k2_funct_1(sK0)) != X0 | ~r1_tarski(k2_relat_1(sK0),X0)) ) | ~spl1_4),
% 0.21/0.54    inference(forward_demodulation,[],[f136,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(sK0)) | ~r1_tarski(k2_relat_1(sK0),X0)) ) | ~spl1_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f135,f33])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(sK0)) | ~r1_tarski(k2_relat_1(sK0),X0) | ~v1_relat_1(sK0)) ) | ~spl1_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f134,f37])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(sK0)) | ~r1_tarski(k2_relat_1(sK0),X0) | ~v1_relat_1(sK0)) ) | ~spl1_4),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f129])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k1_relat_1(sK0) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(sK0)) | ~r1_tarski(k2_relat_1(sK0),X0) | ~v1_relat_1(sK0)) ) | ~spl1_4),
% 0.21/0.54    inference(superposition,[],[f121,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X0)) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(k2_funct_1(sK0))) ) | ~spl1_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f120])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    spl1_4 <=> ! [X0] : (k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X0)) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(k2_funct_1(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    spl1_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    $false | spl1_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f126,f33])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ~v1_relat_1(sK0) | spl1_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f125,f34])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 0.21/0.54    inference(resolution,[],[f118,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ~v1_relat_1(k2_funct_1(sK0)) | spl1_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f116])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ~spl1_3 | spl1_4 | spl1_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f123,f57,f120,f116])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    spl1_1 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X0)) | k1_relat_1(X0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | spl1_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f98,f33])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X0)) | k1_relat_1(X0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | spl1_1),
% 0.21/0.54    inference(superposition,[],[f59,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f57])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ~spl1_1 | ~spl1_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f61,f57])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (29186)------------------------------
% 0.21/0.54  % (29186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29186)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (29186)Memory used [KB]: 6268
% 0.21/0.54  % (29186)Time elapsed: 0.115 s
% 0.21/0.54  % (29186)------------------------------
% 0.21/0.54  % (29186)------------------------------
% 0.21/0.54  % (29199)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (29181)Success in time 0.177 s
%------------------------------------------------------------------------------
