%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 330 expanded)
%              Number of leaves         :   17 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  336 (2200 expanded)
%              Number of equality atoms :   87 ( 814 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f389,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f166,f171,f305,f313,f385])).

fof(f385,plain,
    ( ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f383,f36])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k2_funct_1(sK1) != sK2
    & k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK2,sK1)
    & k1_relat_1(sK1) = k2_relat_1(sK2)
    & v2_funct_1(sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK1) != X1
          & k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(X1,sK1)
          & k2_relat_1(X1) = k1_relat_1(sK1)
          & v2_funct_1(sK1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( k2_funct_1(sK1) != X1
        & k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(X1,sK1)
        & k2_relat_1(X1) = k1_relat_1(sK1)
        & v2_funct_1(sK1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK1) != sK2
      & k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK2,sK1)
      & k1_relat_1(sK1) = k2_relat_1(sK2)
      & v2_funct_1(sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f383,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f377,f86])).

fof(f86,plain,(
    sK2 != k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f85,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,
    ( sK2 != k4_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f84,f35])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,
    ( sK2 != k4_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f80,f38])).

fof(f38,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,
    ( sK2 != k4_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f41,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f41,plain,(
    k2_funct_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f377,plain,
    ( sK2 = k4_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f46,f374])).

fof(f374,plain,
    ( k4_relat_1(sK1) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f373,f164])).

fof(f164,plain,
    ( k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl3_5
  <=> k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f373,plain,
    ( k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f372,f34])).

fof(f372,plain,
    ( k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))
    | ~ v1_relat_1(sK1)
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f371,f35])).

fof(f371,plain,
    ( k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f370,f38])).

fof(f370,plain,
    ( k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_9 ),
    inference(superposition,[],[f304,f53])).

fof(f304,plain,
    ( k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl3_9
  <=> k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f46,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f313,plain,
    ( ~ spl3_4
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f311,f34])).

fof(f311,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f310,f35])).

fof(f310,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f309,f38])).

fof(f309,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f308,f159])).

fof(f159,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl3_4
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f308,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_8 ),
    inference(superposition,[],[f300,f53])).

fof(f300,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl3_8
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f305,plain,
    ( ~ spl3_8
    | spl3_9 ),
    inference(avatar_split_clause,[],[f296,f302,f298])).

fof(f296,plain,
    ( k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f295,f39])).

fof(f39,plain,(
    k1_relat_1(sK1) = k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f295,plain,
    ( k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f294,f34])).

fof(f294,plain,
    ( k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f293,f35])).

fof(f293,plain,
    ( k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f285,f38])).

fof(f285,plain,
    ( k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f253,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f253,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k2_relat_1(sK1)) = k5_relat_1(sK2,k5_relat_1(sK1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f252,f36])).

fof(f252,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k2_relat_1(sK1)) = k5_relat_1(sK2,k5_relat_1(sK1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f236,f34])).

fof(f236,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k2_relat_1(sK1)) = k5_relat_1(sK2,k5_relat_1(sK1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2) ) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k2_relat_1(sK1)) = k5_relat_1(sK2,k5_relat_1(sK1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f48,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k2_relat_1(sK1)) = k5_relat_1(k5_relat_1(sK2,sK1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f56,f40])).

fof(f40,plain,(
    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
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
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f171,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f169,f34])).

fof(f169,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_4 ),
    inference(subsumption_resolution,[],[f168,f35])).

fof(f168,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_4 ),
    inference(subsumption_resolution,[],[f167,f38])).

fof(f167,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_4 ),
    inference(resolution,[],[f160,f89])).

fof(f89,plain,(
    ! [X2] :
      ( v1_relat_1(k4_relat_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f83,f52])).

fof(f52,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f21,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f83,plain,(
    ! [X2] :
      ( v1_relat_1(k4_relat_1(X2))
      | ~ sP0(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f49,f53])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f160,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f166,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f156,f162,f158])).

fof(f156,plain,
    ( k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))
    | ~ v1_relat_1(k4_relat_1(sK1)) ),
    inference(superposition,[],[f65,f118])).

fof(f118,plain,(
    k4_relat_1(sK1) = k5_relat_1(k5_relat_1(sK2,sK1),k4_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f106,f34])).

fof(f106,plain,
    ( k4_relat_1(sK1) = k5_relat_1(k5_relat_1(sK2,sK1),k4_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f101,f64])).

fof(f64,plain,(
    sK1 = k5_relat_1(sK1,k5_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f63,f34])).

fof(f63,plain,
    ( sK1 = k5_relat_1(sK1,k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f46,f40])).

fof(f101,plain,(
    ! [X2] :
      ( k4_relat_1(k5_relat_1(X2,k5_relat_1(sK2,sK1))) = k5_relat_1(k5_relat_1(sK2,sK1),k4_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f97,f58])).

fof(f58,plain,(
    v1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f43,f40])).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f97,plain,(
    ! [X2] :
      ( k4_relat_1(k5_relat_1(X2,k5_relat_1(sK2,sK1))) = k5_relat_1(k5_relat_1(sK2,sK1),k4_relat_1(X2))
      | ~ v1_relat_1(k5_relat_1(sK2,sK1))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f47,f60])).

fof(f60,plain,(
    k5_relat_1(sK2,sK1) = k4_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f42,f40])).

fof(f42,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (10567)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.48  % (10573)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.48  % (10554)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (10554)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f389,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f166,f171,f305,f313,f385])).
% 0.21/0.49  fof(f385,plain,(
% 0.21/0.49    ~spl3_5 | ~spl3_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f384])).
% 0.21/0.49  fof(f384,plain,(
% 0.21/0.49    $false | (~spl3_5 | ~spl3_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f383,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    (k2_funct_1(sK1) != sK2 & k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK2,sK1) & k1_relat_1(sK1) = k2_relat_1(sK2) & v2_funct_1(sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f31,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK1) != X1 & k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(X1,sK1) & k2_relat_1(X1) = k1_relat_1(sK1) & v2_funct_1(sK1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X1] : (k2_funct_1(sK1) != X1 & k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(X1,sK1) & k2_relat_1(X1) = k1_relat_1(sK1) & v2_funct_1(sK1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK1) != sK2 & k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK2,sK1) & k1_relat_1(sK1) = k2_relat_1(sK2) & v2_funct_1(sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.21/0.49  fof(f383,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | (~spl3_5 | ~spl3_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f377,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    sK2 != k4_relat_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f85,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    sK2 != k4_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f84,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    sK2 != k4_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v2_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    sK2 != k4_relat_1(sK1) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(superposition,[],[f41,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    k2_funct_1(sK1) != sK2),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f377,plain,(
% 0.21/0.49    sK2 = k4_relat_1(sK1) | ~v1_relat_1(sK2) | (~spl3_5 | ~spl3_9)),
% 0.21/0.49    inference(superposition,[],[f46,f374])).
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    k4_relat_1(sK1) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) | (~spl3_5 | ~spl3_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f373,f164])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl3_5 <=> k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f373,plain,(
% 0.21/0.49    k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) | ~spl3_9),
% 0.21/0.49    inference(subsumption_resolution,[],[f372,f34])).
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) | ~v1_relat_1(sK1) | ~spl3_9),
% 0.21/0.49    inference(subsumption_resolution,[],[f371,f35])).
% 0.21/0.49  fof(f371,plain,(
% 0.21/0.49    k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_9),
% 0.21/0.49    inference(subsumption_resolution,[],[f370,f38])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_9),
% 0.21/0.49    inference(superposition,[],[f304,f53])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f302])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    spl3_9 <=> k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    ~spl3_4 | spl3_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f312])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    $false | (~spl3_4 | spl3_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f311,f34])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | (~spl3_4 | spl3_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f310,f35])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_4 | spl3_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f309,f38])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_4 | spl3_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f308,f159])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    v1_relat_1(k4_relat_1(sK1)) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f158])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    spl3_4 <=> v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    ~v1_relat_1(k4_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl3_8),
% 0.21/0.49    inference(superposition,[],[f300,f53])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    ~v1_relat_1(k2_funct_1(sK1)) | spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f298])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    spl3_8 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    ~spl3_8 | spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f296,f302,f298])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.49    inference(forward_demodulation,[],[f295,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    k1_relat_1(sK1) = k2_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f294,f34])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f293,f35])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f285,f38])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    k7_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(k1_relat_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(superposition,[],[f253,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(X0,k2_relat_1(sK1)) = k5_relat_1(sK2,k5_relat_1(sK1,X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f252,f36])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(X0,k2_relat_1(sK1)) = k5_relat_1(sK2,k5_relat_1(sK1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f236,f34])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(X0,k2_relat_1(sK1)) = k5_relat_1(sK2,k5_relat_1(sK1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f222])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(X0,k2_relat_1(sK1)) = k5_relat_1(sK2,k5_relat_1(sK1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(superposition,[],[f48,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(X0,k2_relat_1(sK1)) = k5_relat_1(k5_relat_1(sK2,sK1),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(superposition,[],[f56,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK2,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    $false | spl3_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f169,f34])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl3_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f168,f35])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl3_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f167,f38])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl3_4),
% 0.21/0.49    inference(resolution,[],[f160,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X2] : (v1_relat_1(k4_relat_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f83,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(definition_folding,[],[f21,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X2] : (v1_relat_1(k4_relat_1(X2)) | ~sP0(X2) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(superposition,[],[f49,f53])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f28])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~v1_relat_1(k4_relat_1(sK1)) | spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f158])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ~spl3_4 | spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f156,f162,f158])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    k4_relat_1(sK1) = k7_relat_1(k4_relat_1(sK1),k2_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.49    inference(superposition,[],[f65,f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    k4_relat_1(sK1) = k5_relat_1(k5_relat_1(sK2,sK1),k4_relat_1(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f106,f34])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    k4_relat_1(sK1) = k5_relat_1(k5_relat_1(sK2,sK1),k4_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(superposition,[],[f101,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    sK1 = k5_relat_1(sK1,k5_relat_1(sK2,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f63,f34])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    sK1 = k5_relat_1(sK1,k5_relat_1(sK2,sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(superposition,[],[f46,f40])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X2] : (k4_relat_1(k5_relat_1(X2,k5_relat_1(sK2,sK1))) = k5_relat_1(k5_relat_1(sK2,sK1),k4_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f97,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    v1_relat_1(k5_relat_1(sK2,sK1))),
% 0.21/0.49    inference(superposition,[],[f43,f40])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X2] : (k4_relat_1(k5_relat_1(X2,k5_relat_1(sK2,sK1))) = k5_relat_1(k5_relat_1(sK2,sK1),k4_relat_1(X2)) | ~v1_relat_1(k5_relat_1(sK2,sK1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(superposition,[],[f47,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    k5_relat_1(sK2,sK1) = k4_relat_1(k5_relat_1(sK2,sK1))),
% 0.21/0.49    inference(superposition,[],[f42,f40])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (10554)------------------------------
% 0.21/0.49  % (10554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10554)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (10554)Memory used [KB]: 6268
% 0.21/0.49  % (10554)Time elapsed: 0.086 s
% 0.21/0.49  % (10554)------------------------------
% 0.21/0.49  % (10554)------------------------------
% 0.21/0.49  % (10560)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (10549)Success in time 0.135 s
%------------------------------------------------------------------------------
