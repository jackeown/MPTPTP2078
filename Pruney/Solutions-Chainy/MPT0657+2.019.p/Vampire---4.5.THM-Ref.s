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
% DateTime   : Thu Dec  3 12:53:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 294 expanded)
%              Number of leaves         :   14 (  62 expanded)
%              Depth                    :   20
%              Number of atoms          :  357 (1440 expanded)
%              Number of equality atoms :  102 ( 508 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f447,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f243,f257,f426,f442])).

fof(f442,plain,
    ( ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f440,f34])).

fof(f34,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f440,plain,
    ( sK1 = k2_funct_1(sK0)
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f439,f73])).

fof(f73,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_1
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f439,plain,
    ( k2_relat_1(sK0) != k1_relat_1(sK1)
    | sK1 = k2_funct_1(sK0)
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f438,f30])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f438,plain,
    ( ~ v1_funct_1(sK1)
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | sK1 = k2_funct_1(sK0)
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f331,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f331,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK0) != k1_relat_1(sK1)
    | sK1 = k2_funct_1(sK0)
    | ~ spl2_9 ),
    inference(equality_resolution,[],[f271])).

fof(f271,plain,
    ( ! [X0] :
        ( k5_relat_1(sK0,X0) != k5_relat_1(sK0,sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK0)
        | k2_funct_1(sK0) = X0 )
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f55,f267])).

fof(f267,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1)
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f258,f29])).

fof(f258,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_9 ),
    inference(superposition,[],[f242,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f242,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl2_9
  <=> k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f55,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK0)
      | k2_funct_1(sK0) = X0 ) ),
    inference(subsumption_resolution,[],[f54,f35])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(sK0)
      | k2_funct_1(sK0) = X0 ) ),
    inference(subsumption_resolution,[],[f53,f31])).

fof(f31,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(sK0)
      | k1_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(sK0)
      | k2_funct_1(sK0) = X0 ) ),
    inference(subsumption_resolution,[],[f51,f36])).

fof(f36,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) != k6_relat_1(k2_relat_1(sK1))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(sK0)
      | k1_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(sK0)
      | k2_funct_1(sK0) = X0 ) ),
    inference(superposition,[],[f50,f32])).

fof(f32,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f426,plain,
    ( spl2_2
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f424,f77])).

fof(f77,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl2_2
  <=> r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f424,plain,
    ( r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f423,f338])).

fof(f338,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(superposition,[],[f39,f267])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f423,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f422,f340])).

fof(f340,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(superposition,[],[f37,f267])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f422,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f421,f30])).

fof(f421,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f420,f29])).

fof(f420,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f401,f341])).

fof(f341,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(superposition,[],[f38,f267])).

fof(f38,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f401,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_9 ),
    inference(trivial_inequality_removal,[],[f398])).

fof(f398,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_9 ),
    inference(superposition,[],[f49,f342])).

fof(f342,plain,
    ( sK1 = k5_relat_1(sK1,k5_relat_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f337,f29])).

fof(f337,plain,
    ( sK1 = k5_relat_1(sK1,k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl2_9 ),
    inference(superposition,[],[f41,f267])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(f257,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl2_8 ),
    inference(subsumption_resolution,[],[f255,f35])).

fof(f255,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_8 ),
    inference(subsumption_resolution,[],[f254,f36])).

fof(f254,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_8 ),
    inference(resolution,[],[f238,f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f238,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl2_8
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f243,plain,
    ( ~ spl2_8
    | spl2_9 ),
    inference(avatar_split_clause,[],[f234,f240,f236])).

fof(f234,plain,
    ( k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(forward_demodulation,[],[f233,f32])).

fof(f233,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f232,f35])).

fof(f232,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f231,f31])).

fof(f231,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f224,f36])).

fof(f224,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0))))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f197,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f197,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(sK1,k5_relat_1(sK0,X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f196,f29])).

fof(f196,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(sK1,k5_relat_1(sK0,X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f195,f35])).

fof(f195,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(sK1,k5_relat_1(sK0,X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(sK1,k5_relat_1(sK0,X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f138,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
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
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f138,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k5_relat_1(sK1,sK0),X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f137,f35])).

fof(f137,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k5_relat_1(sK1,sK0),X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f59])).

fof(f59,plain,(
    v1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f37,f33])).

fof(f33,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f114,plain,(
    ! [X0] :
      ( k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k5_relat_1(sK1,sK0),X0))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f43,f61])).

fof(f61,plain,(
    sK0 = k5_relat_1(sK0,k5_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f56,f35])).

fof(f56,plain,
    ( sK0 = k5_relat_1(sK0,k5_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f41,f33])).

fof(f88,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f87,f75,f71])).

fof(f87,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f86,f32])).

fof(f86,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f85,f29])).

fof(f85,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f64,f35])).

fof(f64,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f42,f57])).

fof(f57,plain,(
    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f39,f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:57:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (11911)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.45  % (11911)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.46  % (11930)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (11910)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (11922)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f447,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f88,f243,f257,f426,f442])).
% 0.22/0.47  fof(f442,plain,(
% 0.22/0.47    ~spl2_1 | ~spl2_9),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f441])).
% 0.22/0.47  fof(f441,plain,(
% 0.22/0.47    $false | (~spl2_1 | ~spl2_9)),
% 0.22/0.47    inference(subsumption_resolution,[],[f440,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    sK1 != k2_funct_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f11])).
% 0.22/0.47  fof(f11,conjecture,(
% 0.22/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.22/0.47  fof(f440,plain,(
% 0.22/0.47    sK1 = k2_funct_1(sK0) | (~spl2_1 | ~spl2_9)),
% 0.22/0.47    inference(subsumption_resolution,[],[f439,f73])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f71])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    spl2_1 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f439,plain,(
% 0.22/0.47    k2_relat_1(sK0) != k1_relat_1(sK1) | sK1 = k2_funct_1(sK0) | ~spl2_9),
% 0.22/0.47    inference(subsumption_resolution,[],[f438,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    v1_funct_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f438,plain,(
% 0.22/0.47    ~v1_funct_1(sK1) | k2_relat_1(sK0) != k1_relat_1(sK1) | sK1 = k2_funct_1(sK0) | ~spl2_9),
% 0.22/0.47    inference(subsumption_resolution,[],[f331,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    v1_relat_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f331,plain,(
% 0.22/0.47    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k2_relat_1(sK0) != k1_relat_1(sK1) | sK1 = k2_funct_1(sK0) | ~spl2_9),
% 0.22/0.47    inference(equality_resolution,[],[f271])).
% 0.22/0.47  fof(f271,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) != k5_relat_1(sK0,sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | k2_funct_1(sK0) = X0) ) | ~spl2_9),
% 0.22/0.47    inference(backward_demodulation,[],[f55,f267])).
% 0.22/0.47  fof(f267,plain,(
% 0.22/0.47    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1) | ~spl2_9),
% 0.22/0.47    inference(subsumption_resolution,[],[f258,f29])).
% 0.22/0.47  fof(f258,plain,(
% 0.22/0.47    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,sK1) | ~v1_relat_1(sK1) | ~spl2_9),
% 0.22/0.47    inference(superposition,[],[f242,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.47  fof(f242,plain,(
% 0.22/0.47    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))) | ~spl2_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f240])).
% 0.22/0.47  fof(f240,plain,(
% 0.22/0.47    spl2_9 <=> k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) != k6_relat_1(k2_relat_1(sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | k2_funct_1(sK0) = X0) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f54,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    v1_relat_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) != k6_relat_1(k2_relat_1(sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = X0) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f53,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    v2_funct_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) != k6_relat_1(k2_relat_1(sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(sK0) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = X0) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f51,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    v1_funct_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(sK0) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = X0) )),
% 0.22/0.47    inference(superposition,[],[f50,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.22/0.47  fof(f426,plain,(
% 0.22/0.47    spl2_2 | ~spl2_9),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f425])).
% 0.22/0.47  fof(f425,plain,(
% 0.22/0.47    $false | (spl2_2 | ~spl2_9)),
% 0.22/0.47    inference(subsumption_resolution,[],[f424,f77])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f75])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    spl2_2 <=> r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f424,plain,(
% 0.22/0.47    r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | ~spl2_9),
% 0.22/0.47    inference(forward_demodulation,[],[f423,f338])).
% 0.22/0.47  fof(f338,plain,(
% 0.22/0.47    k2_relat_1(sK1) = k1_relat_1(k5_relat_1(sK0,sK1)) | ~spl2_9),
% 0.22/0.47    inference(superposition,[],[f39,f267])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.47  fof(f423,plain,(
% 0.22/0.47    r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_9),
% 0.22/0.47    inference(subsumption_resolution,[],[f422,f340])).
% 0.22/0.47  fof(f340,plain,(
% 0.22/0.47    v1_relat_1(k5_relat_1(sK0,sK1)) | ~spl2_9),
% 0.22/0.47    inference(superposition,[],[f37,f267])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.47  fof(f422,plain,(
% 0.22/0.47    ~v1_relat_1(k5_relat_1(sK0,sK1)) | r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_9),
% 0.22/0.47    inference(subsumption_resolution,[],[f421,f30])).
% 0.22/0.47  fof(f421,plain,(
% 0.22/0.47    ~v1_funct_1(sK1) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_9),
% 0.22/0.47    inference(subsumption_resolution,[],[f420,f29])).
% 0.22/0.47  fof(f420,plain,(
% 0.22/0.47    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_9),
% 0.22/0.47    inference(subsumption_resolution,[],[f401,f341])).
% 0.22/0.47  fof(f341,plain,(
% 0.22/0.47    v1_funct_1(k5_relat_1(sK0,sK1)) | ~spl2_9),
% 0.22/0.47    inference(superposition,[],[f38,f267])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f401,plain,(
% 0.22/0.47    ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_9),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f398])).
% 0.22/0.47  fof(f398,plain,(
% 0.22/0.47    k1_relat_1(sK1) != k1_relat_1(sK1) | ~v1_funct_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | r1_tarski(k2_relat_1(sK1),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_9),
% 0.22/0.47    inference(superposition,[],[f49,f342])).
% 0.22/0.47  fof(f342,plain,(
% 0.22/0.47    sK1 = k5_relat_1(sK1,k5_relat_1(sK0,sK1)) | ~spl2_9),
% 0.22/0.47    inference(subsumption_resolution,[],[f337,f29])).
% 0.22/0.47  fof(f337,plain,(
% 0.22/0.47    sK1 = k5_relat_1(sK1,k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK1) | ~spl2_9),
% 0.22/0.47    inference(superposition,[],[f41,f267])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
% 0.22/0.47  fof(f257,plain,(
% 0.22/0.47    spl2_8),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f256])).
% 0.22/0.47  fof(f256,plain,(
% 0.22/0.47    $false | spl2_8),
% 0.22/0.47    inference(subsumption_resolution,[],[f255,f35])).
% 0.22/0.47  fof(f255,plain,(
% 0.22/0.47    ~v1_relat_1(sK0) | spl2_8),
% 0.22/0.47    inference(subsumption_resolution,[],[f254,f36])).
% 0.22/0.47  fof(f254,plain,(
% 0.22/0.47    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl2_8),
% 0.22/0.47    inference(resolution,[],[f238,f44])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.47  fof(f238,plain,(
% 0.22/0.47    ~v1_relat_1(k2_funct_1(sK0)) | spl2_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f236])).
% 0.22/0.47  fof(f236,plain,(
% 0.22/0.47    spl2_8 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.47  fof(f243,plain,(
% 0.22/0.47    ~spl2_8 | spl2_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f234,f240,f236])).
% 0.22/0.47  fof(f234,plain,(
% 0.22/0.47    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))) | ~v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.47    inference(forward_demodulation,[],[f233,f32])).
% 0.22/0.47  fof(f233,plain,(
% 0.22/0.47    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))) | ~v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.47    inference(subsumption_resolution,[],[f232,f35])).
% 0.22/0.47  fof(f232,plain,(
% 0.22/0.47    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f231,f31])).
% 0.22/0.47  fof(f231,plain,(
% 0.22/0.47    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f224,f36])).
% 0.22/0.47  fof(f224,plain,(
% 0.22/0.47    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k5_relat_1(sK1,k6_relat_1(k1_relat_1(sK0)))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.47    inference(superposition,[],[f197,f46])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.47  fof(f197,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(sK1,k5_relat_1(sK0,X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f196,f29])).
% 0.22/0.47  fof(f196,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(sK1,k5_relat_1(sK0,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(sK1)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f195,f35])).
% 0.22/0.47  fof(f195,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(sK1,k5_relat_1(sK0,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f186])).
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(sK1,k5_relat_1(sK0,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_relat_1(sK1)) )),
% 0.22/0.47    inference(superposition,[],[f138,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.22/0.47  fof(f138,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k5_relat_1(sK1,sK0),X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f137,f35])).
% 0.22/0.47  fof(f137,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k5_relat_1(sK1,sK0),X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f114,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    v1_relat_1(k5_relat_1(sK1,sK0))),
% 0.22/0.47    inference(superposition,[],[f37,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relat_1(sK0,X0) = k5_relat_1(sK0,k5_relat_1(k5_relat_1(sK1,sK0),X0)) | ~v1_relat_1(k5_relat_1(sK1,sK0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) )),
% 0.22/0.47    inference(superposition,[],[f43,f61])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    sK0 = k5_relat_1(sK0,k5_relat_1(sK1,sK0))),
% 0.22/0.47    inference(subsumption_resolution,[],[f56,f35])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    sK0 = k5_relat_1(sK0,k5_relat_1(sK1,sK0)) | ~v1_relat_1(sK0)),
% 0.22/0.47    inference(superposition,[],[f41,f33])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    spl2_1 | ~spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f87,f75,f71])).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.47    inference(forward_demodulation,[],[f86,f32])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    k2_relat_1(sK0) = k1_relat_1(sK1) | ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))),
% 0.22/0.47    inference(subsumption_resolution,[],[f85,f29])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    k2_relat_1(sK0) = k1_relat_1(sK1) | ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f64,f35])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    k2_relat_1(sK0) = k1_relat_1(sK1) | ~v1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.47    inference(superposition,[],[f42,f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(sK1,sK0))),
% 0.22/0.47    inference(superposition,[],[f39,f33])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (11911)------------------------------
% 0.22/0.47  % (11911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (11911)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (11911)Memory used [KB]: 10746
% 0.22/0.47  % (11911)Time elapsed: 0.050 s
% 0.22/0.47  % (11911)------------------------------
% 0.22/0.47  % (11911)------------------------------
% 0.22/0.47  % (11901)Success in time 0.105 s
%------------------------------------------------------------------------------
