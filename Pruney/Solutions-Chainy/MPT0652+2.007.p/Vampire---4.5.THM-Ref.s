%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 223 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  355 ( 937 expanded)
%              Number of equality atoms :  102 ( 328 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f134,f138,f207,f213,f275,f359])).

fof(f359,plain,
    ( spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(trivial_inequality_removal,[],[f357])).

fof(f357,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(resolution,[],[f348,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f348,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | k1_relat_1(sK0) != X0 )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f347,f35])).

fof(f35,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f347,plain,
    ( ! [X0] :
        ( k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0)
        | ~ r1_tarski(k1_relat_1(sK0),X0) )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f346,f29])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f346,plain,
    ( ! [X0] :
        ( k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0)
        | ~ r1_tarski(k1_relat_1(sK0),X0)
        | ~ v1_relat_1(sK0) )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f345,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f345,plain,
    ( ! [X0] :
        ( k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ r1_tarski(k1_relat_1(sK0),X0)
        | ~ v1_relat_1(sK0) )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(trivial_inequality_removal,[],[f340])).

fof(f340,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(sK0)
        | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ r1_tarski(k1_relat_1(sK0),X0)
        | ~ v1_relat_1(sK0) )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(superposition,[],[f338,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f338,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f266,f277])).

fof(f277,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_5 ),
    inference(superposition,[],[f198,f34])).

fof(f34,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f198,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl1_5
  <=> k1_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f266,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f265,f127])).

fof(f127,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl1_3
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f265,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_2 ),
    inference(subsumption_resolution,[],[f263,f29])).

fof(f263,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_2 ),
    inference(superposition,[],[f56,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f56,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f275,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl1_5 ),
    inference(subsumption_resolution,[],[f273,f29])).

fof(f273,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(subsumption_resolution,[],[f272,f30])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f272,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(subsumption_resolution,[],[f271,f31])).

fof(f31,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f271,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(subsumption_resolution,[],[f269,f34])).

fof(f269,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(superposition,[],[f199,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f199,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f197])).

fof(f213,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl1_6 ),
    inference(subsumption_resolution,[],[f211,f29])).

fof(f211,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f210,f30])).

fof(f210,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f209,f31])).

fof(f209,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(trivial_inequality_removal,[],[f208])).

fof(f208,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(superposition,[],[f203,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f203,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl1_6
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f207,plain,
    ( ~ spl1_6
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f193,f130,f201])).

fof(f130,plain,
    ( spl1_4
  <=> ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f193,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f192,f29])).

fof(f192,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f191,f30])).

fof(f191,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f190,f31])).

fof(f190,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f189,f34])).

fof(f189,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f183,f33])).

fof(f183,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(superposition,[],[f131,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f61,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f61,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f36,f42])).

fof(f36,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f131,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK0) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f138,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f136,f29])).

fof(f136,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f135,f30])).

fof(f135,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f128,f39])).

fof(f128,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f134,plain,
    ( ~ spl1_3
    | spl1_4
    | spl1_1 ),
    inference(avatar_split_clause,[],[f133,f50,f130,f126])).

fof(f50,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f133,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_1 ),
    inference(subsumption_resolution,[],[f90,f29])).

fof(f90,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | spl1_1 ),
    inference(superposition,[],[f52,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(f52,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f57,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f32,f54,f50])).

fof(f32,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (8755)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.47  % (8746)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.47  % (8762)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.48  % (8749)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % (8756)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.49  % (8764)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.49  % (8761)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.49  % (8770)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.49  % (8759)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (8751)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (8746)Refutation not found, incomplete strategy% (8746)------------------------------
% 0.21/0.50  % (8746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8763)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (8746)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8746)Memory used [KB]: 10746
% 0.21/0.50  % (8746)Time elapsed: 0.075 s
% 0.21/0.50  % (8746)------------------------------
% 0.21/0.50  % (8746)------------------------------
% 0.21/0.50  % (8748)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (8749)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f57,f134,f138,f207,f213,f275,f359])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    spl1_2 | ~spl1_3 | ~spl1_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f358])).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    $false | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f357])).
% 0.21/0.50  fof(f357,plain,(
% 0.21/0.50    k1_relat_1(sK0) != k1_relat_1(sK0) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 0.21/0.50    inference(resolution,[],[f348,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f348,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | k1_relat_1(sK0) != X0) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 0.21/0.50    inference(forward_demodulation,[],[f347,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.50  fof(f347,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),X0)) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f346,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    v1_relat_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),X0) | ~v1_relat_1(sK0)) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f345,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.50  fof(f345,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k1_relat_1(sK0),X0) | ~v1_relat_1(sK0)) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f340])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(sK0) | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k1_relat_1(sK0),X0) | ~v1_relat_1(sK0)) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 0.21/0.50    inference(superposition,[],[f338,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.50  fof(f338,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k1_relat_1(sK0) | ~v1_relat_1(X0)) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 0.21/0.50    inference(forward_demodulation,[],[f266,f277])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_5),
% 0.21/0.50    inference(superposition,[],[f198,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    k1_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~spl1_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f197])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    spl1_5 <=> k1_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f265,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    v1_relat_1(k2_funct_1(sK0)) | ~spl1_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl1_3 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | spl1_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f263,f29])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | spl1_2),
% 0.21/0.50    inference(superposition,[],[f56,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl1_2 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    spl1_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f274])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    $false | spl1_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f273,f29])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ~v1_relat_1(sK0) | spl1_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f272,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    v1_funct_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f271,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    v2_funct_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f269,f34])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_5),
% 0.21/0.50    inference(superposition,[],[f199,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | spl1_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f197])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    spl1_6),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f212])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    $false | spl1_6),
% 0.21/0.50    inference(subsumption_resolution,[],[f211,f29])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ~v1_relat_1(sK0) | spl1_6),
% 0.21/0.50    inference(subsumption_resolution,[],[f210,f30])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 0.21/0.50    inference(subsumption_resolution,[],[f209,f31])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f208])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    k2_relat_1(sK0) != k2_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 0.21/0.50    inference(superposition,[],[f203,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | spl1_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f201])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    spl1_6 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ~spl1_6 | ~spl1_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f193,f130,f201])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl1_4 <=> ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~spl1_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f192,f29])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f191,f30])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f190,f31])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f189,f34])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f183,f33])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(k6_relat_1(k1_relat_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.50    inference(superposition,[],[f131,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f61,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(superposition,[],[f36,f42])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(sK0)) ) | ~spl1_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f130])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl1_3),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    $false | spl1_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f136,f29])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ~v1_relat_1(sK0) | spl1_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f135,f30])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 0.21/0.50    inference(resolution,[],[f128,f39])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ~v1_relat_1(k2_funct_1(sK0)) | spl1_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ~spl1_3 | spl1_4 | spl1_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f133,f50,f130,f126])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl1_1 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) | k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | spl1_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f90,f29])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) | k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(X0)) ) | spl1_1),
% 0.21/0.50    inference(superposition,[],[f52,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f50])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ~spl1_1 | ~spl1_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f54,f50])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8749)------------------------------
% 0.21/0.50  % (8749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8749)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8749)Memory used [KB]: 6268
% 0.21/0.50  % (8749)Time elapsed: 0.100 s
% 0.21/0.50  % (8749)------------------------------
% 0.21/0.50  % (8749)------------------------------
% 0.21/0.50  % (8744)Success in time 0.146 s
%------------------------------------------------------------------------------
