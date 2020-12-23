%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 223 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  356 ( 939 expanded)
%              Number of equality atoms :  102 ( 328 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f136,f140,f209,f215,f277,f358])).

fof(f358,plain,
    ( spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(trivial_inequality_removal,[],[f356])).

fof(f356,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(resolution,[],[f347,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
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

fof(f347,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | k1_relat_1(sK0) != X0 )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f346,f36])).

fof(f36,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f346,plain,
    ( ! [X0] :
        ( k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0)
        | ~ r1_tarski(k1_relat_1(sK0),X0) )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f345,f29])).

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

% (21136)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f345,plain,
    ( ! [X0] :
        ( k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0)
        | ~ r1_tarski(k1_relat_1(sK0),X0)
        | ~ v1_relat_1(sK0) )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f344,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f344,plain,
    ( ! [X0] :
        ( k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ r1_tarski(k1_relat_1(sK0),X0)
        | ~ v1_relat_1(sK0) )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(trivial_inequality_removal,[],[f339])).

fof(f339,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(sK0)
        | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ r1_tarski(k1_relat_1(sK0),X0)
        | ~ v1_relat_1(sK0) )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(superposition,[],[f337,f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f337,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f268,f279])).

fof(f279,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_5 ),
    inference(superposition,[],[f200,f35])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f200,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl1_5
  <=> k1_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f268,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f267,f129])).

fof(f129,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl1_3
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f267,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_2 ),
    inference(subsumption_resolution,[],[f265,f29])).

fof(f265,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_2 ),
    inference(superposition,[],[f57,f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(f57,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f277,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl1_5 ),
    inference(subsumption_resolution,[],[f275,f29])).

fof(f275,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(subsumption_resolution,[],[f274,f30])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f274,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(subsumption_resolution,[],[f273,f31])).

fof(f31,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f273,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(subsumption_resolution,[],[f271,f35])).

fof(f271,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(superposition,[],[f201,f43])).

fof(f43,plain,(
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

fof(f201,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f199])).

fof(f215,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl1_6 ),
    inference(subsumption_resolution,[],[f213,f29])).

fof(f213,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f212,f30])).

fof(f212,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f211,f31])).

fof(f211,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(trivial_inequality_removal,[],[f210])).

fof(f210,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(superposition,[],[f205,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f205,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl1_6
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f209,plain,
    ( ~ spl1_6
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f195,f132,f203])).

fof(f132,plain,
    ( spl1_4
  <=> ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f195,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f194,f29])).

fof(f194,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f193,f30])).

fof(f193,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f192,f31])).

fof(f192,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f191,f35])).

fof(f191,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f185,f33])).

fof(f185,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(superposition,[],[f133,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f62,f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f62,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f37,f43])).

fof(f37,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f133,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK0) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f140,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f138,f29])).

fof(f138,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f137,f30])).

fof(f137,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f130,f40])).

fof(f130,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f136,plain,
    ( ~ spl1_3
    | spl1_4
    | spl1_1 ),
    inference(avatar_split_clause,[],[f135,f51,f132,f128])).

fof(f51,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f135,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_1 ),
    inference(subsumption_resolution,[],[f92,f29])).

fof(f92,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | spl1_1 ),
    inference(superposition,[],[f53,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

% (21142)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(f53,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f58,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f32,f55,f51])).

fof(f32,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:45:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (21126)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (21123)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (21125)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (21124)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (21139)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (21125)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (21134)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (21141)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (21133)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (21135)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.22/0.52  % (21122)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.52  % (21140)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.22/0.52  % (21131)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.22/0.52  % (21132)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.22/0.52  % (21127)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.22/0.52  % (21122)Refutation not found, incomplete strategy% (21122)------------------------------
% 1.22/0.52  % (21122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (21121)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.22/0.53  % (21138)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.22/0.53  % (21144)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.22/0.53  % (21130)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.22/0.53  % (21146)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.22/0.54  % SZS output start Proof for theBenchmark
% 1.22/0.54  fof(f359,plain,(
% 1.22/0.54    $false),
% 1.22/0.54    inference(avatar_sat_refutation,[],[f58,f136,f140,f209,f215,f277,f358])).
% 1.22/0.54  fof(f358,plain,(
% 1.22/0.54    spl1_2 | ~spl1_3 | ~spl1_5),
% 1.22/0.54    inference(avatar_contradiction_clause,[],[f357])).
% 1.22/0.54  fof(f357,plain,(
% 1.22/0.54    $false | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 1.22/0.54    inference(trivial_inequality_removal,[],[f356])).
% 1.22/0.54  fof(f356,plain,(
% 1.22/0.54    k1_relat_1(sK0) != k1_relat_1(sK0) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 1.22/0.54    inference(resolution,[],[f347,f48])).
% 1.22/0.54  fof(f48,plain,(
% 1.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.22/0.54    inference(equality_resolution,[],[f46])).
% 1.22/0.54  fof(f46,plain,(
% 1.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.22/0.54    inference(cnf_transformation,[],[f28])).
% 1.22/0.54  fof(f28,plain,(
% 1.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.22/0.54    inference(flattening,[],[f27])).
% 1.22/0.54  fof(f27,plain,(
% 1.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.22/0.54    inference(nnf_transformation,[],[f1])).
% 1.22/0.54  fof(f1,axiom,(
% 1.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.22/0.54  fof(f347,plain,(
% 1.22/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | k1_relat_1(sK0) != X0) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 1.22/0.54    inference(forward_demodulation,[],[f346,f36])).
% 1.22/0.54  fof(f36,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.22/0.54    inference(cnf_transformation,[],[f4])).
% 1.22/0.54  fof(f4,axiom,(
% 1.22/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.22/0.54  fof(f346,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),X0)) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 1.22/0.54    inference(subsumption_resolution,[],[f345,f29])).
% 1.22/0.54  fof(f29,plain,(
% 1.22/0.54    v1_relat_1(sK0)),
% 1.22/0.54    inference(cnf_transformation,[],[f26])).
% 1.22/0.54  fof(f26,plain,(
% 1.22/0.54    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).
% 1.22/0.54  fof(f25,plain,(
% 1.22/0.54    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.22/0.54    introduced(choice_axiom,[])).
% 1.22/0.54  fof(f13,plain,(
% 1.22/0.54    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.22/0.54    inference(flattening,[],[f12])).
% 1.22/0.54  fof(f12,plain,(
% 1.22/0.54    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.22/0.54    inference(ennf_transformation,[],[f11])).
% 1.22/0.54  fof(f11,negated_conjecture,(
% 1.22/0.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.22/0.54    inference(negated_conjecture,[],[f10])).
% 1.22/0.54  % (21136)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.22/0.54  fof(f10,conjecture,(
% 1.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 1.22/0.54  fof(f345,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0) | ~r1_tarski(k1_relat_1(sK0),X0) | ~v1_relat_1(sK0)) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 1.22/0.54    inference(subsumption_resolution,[],[f344,f33])).
% 1.22/0.54  fof(f33,plain,(
% 1.22/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.22/0.54    inference(cnf_transformation,[],[f8])).
% 1.22/0.54  fof(f8,axiom,(
% 1.22/0.54    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.22/0.54  fof(f344,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k1_relat_1(sK0),X0) | ~v1_relat_1(sK0)) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 1.22/0.54    inference(trivial_inequality_removal,[],[f339])).
% 1.22/0.54  fof(f339,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(sK0) | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k1_relat_1(sK0),X0) | ~v1_relat_1(sK0)) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 1.22/0.54    inference(superposition,[],[f337,f44])).
% 1.22/0.54  fof(f44,plain,(
% 1.22/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.22/0.54    inference(cnf_transformation,[],[f24])).
% 1.22/0.54  fof(f24,plain,(
% 1.22/0.54    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.22/0.54    inference(flattening,[],[f23])).
% 1.22/0.54  fof(f23,plain,(
% 1.22/0.54    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.22/0.54    inference(ennf_transformation,[],[f5])).
% 1.22/0.54  fof(f5,axiom,(
% 1.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.22/0.54  fof(f337,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k1_relat_1(sK0) | ~v1_relat_1(X0)) ) | (spl1_2 | ~spl1_3 | ~spl1_5)),
% 1.22/0.54    inference(forward_demodulation,[],[f268,f279])).
% 1.22/0.54  fof(f279,plain,(
% 1.22/0.54    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_5),
% 1.22/0.54    inference(superposition,[],[f200,f35])).
% 1.22/0.54  fof(f35,plain,(
% 1.22/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.22/0.54    inference(cnf_transformation,[],[f4])).
% 1.22/0.54  fof(f200,plain,(
% 1.22/0.54    k1_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~spl1_5),
% 1.22/0.54    inference(avatar_component_clause,[],[f199])).
% 1.22/0.54  fof(f199,plain,(
% 1.22/0.54    spl1_5 <=> k1_relat_1(sK0) = k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))))),
% 1.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.22/0.54  fof(f268,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | (spl1_2 | ~spl1_3)),
% 1.22/0.54    inference(subsumption_resolution,[],[f267,f129])).
% 1.22/0.54  fof(f129,plain,(
% 1.22/0.54    v1_relat_1(k2_funct_1(sK0)) | ~spl1_3),
% 1.22/0.54    inference(avatar_component_clause,[],[f128])).
% 1.22/0.54  fof(f128,plain,(
% 1.22/0.54    spl1_3 <=> v1_relat_1(k2_funct_1(sK0))),
% 1.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.22/0.54  fof(f267,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | spl1_2),
% 1.22/0.54    inference(subsumption_resolution,[],[f265,f29])).
% 1.22/0.54  fof(f265,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | spl1_2),
% 1.22/0.54    inference(superposition,[],[f57,f39])).
% 1.22/0.54  fof(f39,plain,(
% 1.22/0.54    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.22/0.54    inference(cnf_transformation,[],[f18])).
% 1.22/0.54  fof(f18,plain,(
% 1.22/0.54    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.22/0.54    inference(flattening,[],[f17])).
% 1.22/0.54  fof(f17,plain,(
% 1.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.22/0.54    inference(ennf_transformation,[],[f3])).
% 1.22/0.54  fof(f3,axiom,(
% 1.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).
% 1.22/0.54  fof(f57,plain,(
% 1.22/0.54    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_2),
% 1.22/0.54    inference(avatar_component_clause,[],[f55])).
% 1.22/0.54  fof(f55,plain,(
% 1.22/0.54    spl1_2 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.22/0.54  fof(f277,plain,(
% 1.22/0.54    spl1_5),
% 1.22/0.54    inference(avatar_contradiction_clause,[],[f276])).
% 1.22/0.54  fof(f276,plain,(
% 1.22/0.54    $false | spl1_5),
% 1.22/0.54    inference(subsumption_resolution,[],[f275,f29])).
% 1.22/0.54  fof(f275,plain,(
% 1.22/0.54    ~v1_relat_1(sK0) | spl1_5),
% 1.22/0.54    inference(subsumption_resolution,[],[f274,f30])).
% 1.22/0.54  fof(f30,plain,(
% 1.22/0.54    v1_funct_1(sK0)),
% 1.22/0.54    inference(cnf_transformation,[],[f26])).
% 1.22/0.54  fof(f274,plain,(
% 1.22/0.54    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_5),
% 1.22/0.54    inference(subsumption_resolution,[],[f273,f31])).
% 1.22/0.54  fof(f31,plain,(
% 1.22/0.54    v2_funct_1(sK0)),
% 1.22/0.54    inference(cnf_transformation,[],[f26])).
% 1.22/0.54  fof(f273,plain,(
% 1.22/0.54    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_5),
% 1.22/0.54    inference(subsumption_resolution,[],[f271,f35])).
% 1.22/0.54  fof(f271,plain,(
% 1.22/0.54    k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_5),
% 1.22/0.54    inference(superposition,[],[f201,f43])).
% 1.22/0.54  fof(f43,plain,(
% 1.22/0.54    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.54    inference(cnf_transformation,[],[f22])).
% 1.22/0.54  fof(f22,plain,(
% 1.22/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.22/0.54    inference(flattening,[],[f21])).
% 1.22/0.54  fof(f21,plain,(
% 1.22/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.22/0.54    inference(ennf_transformation,[],[f9])).
% 1.22/0.54  fof(f9,axiom,(
% 1.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.22/0.54  fof(f201,plain,(
% 1.22/0.54    k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | spl1_5),
% 1.22/0.54    inference(avatar_component_clause,[],[f199])).
% 1.22/0.54  fof(f215,plain,(
% 1.22/0.54    spl1_6),
% 1.22/0.54    inference(avatar_contradiction_clause,[],[f214])).
% 1.22/0.54  fof(f214,plain,(
% 1.22/0.54    $false | spl1_6),
% 1.22/0.54    inference(subsumption_resolution,[],[f213,f29])).
% 1.22/0.54  fof(f213,plain,(
% 1.22/0.54    ~v1_relat_1(sK0) | spl1_6),
% 1.22/0.54    inference(subsumption_resolution,[],[f212,f30])).
% 1.22/0.54  fof(f212,plain,(
% 1.22/0.54    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 1.22/0.54    inference(subsumption_resolution,[],[f211,f31])).
% 1.22/0.54  fof(f211,plain,(
% 1.22/0.54    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 1.22/0.54    inference(trivial_inequality_removal,[],[f210])).
% 1.22/0.54  fof(f210,plain,(
% 1.22/0.54    k2_relat_1(sK0) != k2_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 1.22/0.54    inference(superposition,[],[f205,f42])).
% 1.22/0.54  fof(f42,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.54    inference(cnf_transformation,[],[f22])).
% 1.22/0.54  fof(f205,plain,(
% 1.22/0.54    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | spl1_6),
% 1.22/0.54    inference(avatar_component_clause,[],[f203])).
% 1.22/0.54  fof(f203,plain,(
% 1.22/0.54    spl1_6 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 1.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.22/0.54  fof(f209,plain,(
% 1.22/0.54    ~spl1_6 | ~spl1_4),
% 1.22/0.54    inference(avatar_split_clause,[],[f195,f132,f203])).
% 1.22/0.54  fof(f132,plain,(
% 1.22/0.54    spl1_4 <=> ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(sK0))),
% 1.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.22/0.54  fof(f195,plain,(
% 1.22/0.54    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~spl1_4),
% 1.22/0.54    inference(subsumption_resolution,[],[f194,f29])).
% 1.22/0.54  fof(f194,plain,(
% 1.22/0.54    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~spl1_4),
% 1.22/0.54    inference(subsumption_resolution,[],[f193,f30])).
% 1.22/0.54  fof(f193,plain,(
% 1.22/0.54    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 1.22/0.54    inference(subsumption_resolution,[],[f192,f31])).
% 1.22/0.54  fof(f192,plain,(
% 1.22/0.54    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 1.22/0.54    inference(subsumption_resolution,[],[f191,f35])).
% 1.22/0.54  fof(f191,plain,(
% 1.22/0.54    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 1.22/0.54    inference(subsumption_resolution,[],[f185,f33])).
% 1.22/0.54  fof(f185,plain,(
% 1.22/0.54    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(k6_relat_1(k1_relat_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_4),
% 1.22/0.54    inference(superposition,[],[f133,f63])).
% 1.22/0.54  fof(f63,plain,(
% 1.22/0.54    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.54    inference(subsumption_resolution,[],[f62,f40])).
% 1.22/0.54  fof(f40,plain,(
% 1.22/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.54    inference(cnf_transformation,[],[f20])).
% 1.22/0.54  fof(f20,plain,(
% 1.22/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.22/0.54    inference(flattening,[],[f19])).
% 1.22/0.54  fof(f19,plain,(
% 1.22/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.22/0.54    inference(ennf_transformation,[],[f7])).
% 1.22/0.54  fof(f7,axiom,(
% 1.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.22/0.54  fof(f62,plain,(
% 1.22/0.54    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_relat_1(k1_relat_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.22/0.54    inference(superposition,[],[f37,f43])).
% 1.22/0.54  fof(f37,plain,(
% 1.22/0.54    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.22/0.54    inference(cnf_transformation,[],[f14])).
% 1.22/0.54  fof(f14,plain,(
% 1.22/0.54    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.22/0.54    inference(ennf_transformation,[],[f6])).
% 1.22/0.54  fof(f6,axiom,(
% 1.22/0.54    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.22/0.54  fof(f133,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) | ~v1_relat_1(X0) | k1_relat_1(X0) != k1_relat_1(sK0)) ) | ~spl1_4),
% 1.22/0.54    inference(avatar_component_clause,[],[f132])).
% 1.22/0.54  fof(f140,plain,(
% 1.22/0.54    spl1_3),
% 1.22/0.54    inference(avatar_contradiction_clause,[],[f139])).
% 1.22/0.54  fof(f139,plain,(
% 1.22/0.54    $false | spl1_3),
% 1.22/0.54    inference(subsumption_resolution,[],[f138,f29])).
% 1.22/0.54  fof(f138,plain,(
% 1.22/0.54    ~v1_relat_1(sK0) | spl1_3),
% 1.22/0.54    inference(subsumption_resolution,[],[f137,f30])).
% 1.22/0.54  fof(f137,plain,(
% 1.22/0.54    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 1.22/0.54    inference(resolution,[],[f130,f40])).
% 1.22/0.54  fof(f130,plain,(
% 1.22/0.54    ~v1_relat_1(k2_funct_1(sK0)) | spl1_3),
% 1.22/0.54    inference(avatar_component_clause,[],[f128])).
% 1.22/0.54  fof(f136,plain,(
% 1.22/0.54    ~spl1_3 | spl1_4 | spl1_1),
% 1.22/0.54    inference(avatar_split_clause,[],[f135,f51,f132,f128])).
% 1.22/0.54  fof(f51,plain,(
% 1.22/0.54    spl1_1 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.22/0.54  fof(f135,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) | k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | spl1_1),
% 1.22/0.54    inference(subsumption_resolution,[],[f92,f29])).
% 1.22/0.54  fof(f92,plain,(
% 1.22/0.54    ( ! [X0] : (k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) | k1_relat_1(X0) != k1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(X0)) ) | spl1_1),
% 1.22/0.54    inference(superposition,[],[f53,f38])).
% 1.22/0.54  fof(f38,plain,(
% 1.22/0.54    ( ! [X2,X0,X1] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.22/0.54    inference(cnf_transformation,[],[f16])).
% 1.22/0.54  % (21142)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.22/0.54  fof(f16,plain,(
% 1.22/0.54    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.22/0.54    inference(flattening,[],[f15])).
% 1.22/0.54  fof(f15,plain,(
% 1.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.22/0.54    inference(ennf_transformation,[],[f2])).
% 1.22/0.54  fof(f2,axiom,(
% 1.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).
% 1.22/0.54  fof(f53,plain,(
% 1.22/0.54    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_1),
% 1.22/0.54    inference(avatar_component_clause,[],[f51])).
% 1.22/0.54  fof(f58,plain,(
% 1.22/0.54    ~spl1_1 | ~spl1_2),
% 1.22/0.54    inference(avatar_split_clause,[],[f32,f55,f51])).
% 1.22/0.54  fof(f32,plain,(
% 1.22/0.54    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.22/0.54    inference(cnf_transformation,[],[f26])).
% 1.22/0.54  % SZS output end Proof for theBenchmark
% 1.22/0.54  % (21125)------------------------------
% 1.22/0.54  % (21125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.54  % (21125)Termination reason: Refutation
% 1.22/0.54  
% 1.22/0.54  % (21125)Memory used [KB]: 6268
% 1.22/0.54  % (21125)Time elapsed: 0.091 s
% 1.22/0.54  % (21125)------------------------------
% 1.22/0.54  % (21125)------------------------------
% 1.37/0.54  % (21120)Success in time 0.17 s
%------------------------------------------------------------------------------
