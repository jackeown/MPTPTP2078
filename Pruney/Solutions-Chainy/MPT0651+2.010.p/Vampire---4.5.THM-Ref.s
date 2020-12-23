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
% DateTime   : Thu Dec  3 12:52:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 201 expanded)
%              Number of leaves         :   16 (  53 expanded)
%              Depth                    :   24
%              Number of atoms          :  319 ( 853 expanded)
%              Number of equality atoms :   86 ( 284 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f91,f113,f119,f188])).

fof(f188,plain,
    ( spl1_2
    | ~ spl1_3 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f186,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f26])).

fof(f26,plain,
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

fof(f14,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f186,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f185,f31])).

fof(f31,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f185,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f184,f32])).

fof(f32,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f184,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(trivial_inequality_removal,[],[f183])).

fof(f183,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f180,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f180,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f179,f30])).

fof(f179,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f178,f31])).

fof(f178,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f176,f32])).

fof(f176,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(trivial_inequality_removal,[],[f174])).

fof(f174,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f172,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f65,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f38,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f172,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),X0)
        | k2_relat_1(sK0) != X0 )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f171,f85])).

fof(f85,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl1_3
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f171,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),X0)
        | k2_relat_1(sK0) != X0
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f168,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f168,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0))
        | k2_relat_1(sK0) != X0 )
    | spl1_2
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f167,f37])).

fof(f37,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f167,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0))
        | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0) )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f166,f85])).

fof(f166,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0))
        | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f161,f34])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f161,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0))
        | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f158,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f158,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
        | k2_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f157,f30])).

fof(f157,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
        | k2_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f155,f85])).

fof(f155,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
        | k2_relat_1(X0) != k2_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | spl1_2 ),
    inference(superposition,[],[f59,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
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
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(f59,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f119,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl1_4 ),
    inference(subsumption_resolution,[],[f117,f30])).

fof(f117,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(subsumption_resolution,[],[f116,f31])).

fof(f116,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(subsumption_resolution,[],[f115,f32])).

fof(f115,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(subsumption_resolution,[],[f114,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f114,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(superposition,[],[f90,f43])).

fof(f90,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0)))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl1_4
  <=> r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f113,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f111,f30])).

fof(f111,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f110,f31])).

fof(f110,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f86,f41])).

fof(f86,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f91,plain,
    ( ~ spl1_3
    | ~ spl1_4
    | spl1_1 ),
    inference(avatar_split_clause,[],[f82,f53,f88,f84])).

fof(f53,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f82,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(subsumption_resolution,[],[f77,f30])).

fof(f77,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(superposition,[],[f55,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f55,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f60,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f33,f57,f53])).

fof(f33,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:18:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (10085)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (10077)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (10086)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (10099)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (10078)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.55  % (10097)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (10082)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (10078)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f60,f91,f113,f119,f188])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    spl1_2 | ~spl1_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f187])).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    $false | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f186,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    v1_relat_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.55    inference(negated_conjecture,[],[f11])).
% 0.21/0.55  fof(f11,conjecture,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.21/0.55  fof(f186,plain,(
% 0.21/0.55    ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f185,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    v1_funct_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f185,plain,(
% 0.21/0.55    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f184,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    v2_funct_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f183])).
% 0.21/0.55  fof(f183,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k1_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(superposition,[],[f180,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.55  fof(f180,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f179,f30])).
% 0.21/0.55  fof(f179,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f178,f31])).
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f176,f32])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f174])).
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0)) | k2_relat_1(sK0) != k2_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(superposition,[],[f172,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f65,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k2_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(superposition,[],[f38,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),X0) | k2_relat_1(sK0) != X0) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f171,f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    v1_relat_1(k2_funct_1(sK0)) | ~spl1_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    spl1_3 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.55  fof(f171,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(sK0) != k9_relat_1(k2_funct_1(sK0),X0) | k2_relat_1(sK0) != X0 | ~v1_relat_1(k2_funct_1(sK0))) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(superposition,[],[f168,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) | k2_relat_1(sK0) != X0) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(forward_demodulation,[],[f167,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0)) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f166,f85])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0))) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f161,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k7_relat_1(k2_funct_1(sK0),X0)) | k2_relat_1(k6_relat_1(X0)) != k2_relat_1(sK0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k2_funct_1(sK0))) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(superposition,[],[f158,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(X0)) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f157,f30])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(X0)) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f155,f85])).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | k2_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(X0)) ) | spl1_2),
% 0.21/0.55    inference(superposition,[],[f59,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    spl1_2 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    spl1_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    $false | spl1_4),
% 0.21/0.55    inference(subsumption_resolution,[],[f117,f30])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ~v1_relat_1(sK0) | spl1_4),
% 0.21/0.55    inference(subsumption_resolution,[],[f116,f31])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_4),
% 0.21/0.55    inference(subsumption_resolution,[],[f115,f32])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_4),
% 0.21/0.55    inference(subsumption_resolution,[],[f114,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_4),
% 0.21/0.55    inference(superposition,[],[f90,f43])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0))) | spl1_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    spl1_4 <=> r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    spl1_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    $false | spl1_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f111,f30])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    ~v1_relat_1(sK0) | spl1_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f110,f31])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 0.21/0.55    inference(resolution,[],[f86,f41])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ~v1_relat_1(k2_funct_1(sK0)) | spl1_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f84])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ~spl1_3 | ~spl1_4 | spl1_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f82,f53,f88,f84])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    spl1_1 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | spl1_1),
% 0.21/0.55    inference(subsumption_resolution,[],[f77,f30])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | spl1_1),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | spl1_1),
% 0.21/0.55    inference(superposition,[],[f55,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f53])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ~spl1_1 | ~spl1_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f33,f57,f53])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (10078)------------------------------
% 0.21/0.55  % (10078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10078)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (10078)Memory used [KB]: 6140
% 0.21/0.55  % (10078)Time elapsed: 0.112 s
% 0.21/0.55  % (10078)------------------------------
% 0.21/0.55  % (10078)------------------------------
% 0.21/0.55  % (10084)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (10083)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (10091)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (10089)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (10095)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (10098)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.56  % (10094)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (10093)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (10090)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.56  % (10073)Success in time 0.193 s
%------------------------------------------------------------------------------
