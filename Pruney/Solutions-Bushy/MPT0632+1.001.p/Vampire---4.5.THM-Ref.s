%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0632+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 220 expanded)
%              Number of leaves         :   15 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  366 ( 844 expanded)
%              Number of equality atoms :   99 ( 308 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f849,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f112,f165,f172,f186,f255,f366,f460,f558,f759,f840,f848])).

fof(f848,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_20
    | spl5_28 ),
    inference(avatar_contradiction_clause,[],[f846])).

fof(f846,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_20
    | spl5_28 ),
    inference(subsumption_resolution,[],[f557,f842])).

fof(f842,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_28 ),
    inference(resolution,[],[f839,f312])).

fof(f312,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f305])).

fof(f305,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f295,f111])).

fof(f111,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) = X2
        | ~ r2_hidden(X2,sK0) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_3
  <=> ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | k1_funct_1(sK1,X2) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f295,plain,
    ( ! [X9] :
        ( r2_hidden(k4_tarski(X9,k1_funct_1(sK1,X9)),sK1)
        | ~ r2_hidden(X9,sK0) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f59,f84])).

fof(f84,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_2
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f59,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X9,k1_funct_1(sK1,X9)),sK1) ) ),
    inference(global_subsumption,[],[f20,f51])).

fof(f51,plain,(
    ! [X9] :
      ( ~ v1_funct_1(sK1)
      | ~ r2_hidden(X9,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X9,k1_funct_1(sK1,X9)),sK1) ) ),
    inference(resolution,[],[f19,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k6_relat_1(X0) = X1
        <=> ( ! [X2] :
                ( r2_hidden(X2,X0)
               => k1_funct_1(X1,X2) = X2 )
            & k1_relat_1(X1) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f20,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f839,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1)
    | spl5_28 ),
    inference(avatar_component_clause,[],[f837])).

fof(f837,plain,
    ( spl5_28
  <=> r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f557,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f555])).

fof(f555,plain,
    ( spl5_20
  <=> r2_hidden(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f840,plain,
    ( ~ spl5_28
    | ~ spl5_20
    | ~ spl5_4
    | spl5_1
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f773,f715,f78,f158,f555,f837])).

fof(f158,plain,
    ( spl5_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f78,plain,
    ( spl5_1
  <=> sK1 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f715,plain,
    ( spl5_27
  <=> sK3(sK0,sK1) = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f773,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK0,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1)
    | spl5_1
    | ~ spl5_27 ),
    inference(trivial_inequality_removal,[],[f762])).

fof(f762,plain,
    ( sK3(sK0,sK1) != sK3(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK0,sK1),sK0)
    | sK1 != sK1
    | ~ r2_hidden(k4_tarski(sK3(sK0,sK1),sK3(sK0,sK1)),sK1)
    | spl5_1
    | ~ spl5_27 ),
    inference(superposition,[],[f269,f717])).

fof(f717,plain,
    ( sK3(sK0,sK1) = sK4(sK0,sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f715])).

fof(f269,plain,
    ( ! [X0] :
        ( sK3(sK0,X0) != sK4(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK3(sK0,X0),sK0)
        | sK1 != X0
        | ~ r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),X0) )
    | spl5_1 ),
    inference(inner_rewriting,[],[f266])).

fof(f266,plain,
    ( ! [X0] :
        ( sK1 != X0
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK3(sK0,X0),sK0)
        | sK3(sK0,X0) != sK4(sK0,X0)
        | ~ r2_hidden(k4_tarski(sK3(sK0,X0),sK4(sK0,X0)),X0) )
    | spl5_1 ),
    inference(superposition,[],[f79,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(sK3(X0,X1),X0)
      | sK3(X0,X1) != sK4(X0,X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f79,plain,
    ( sK1 != k6_relat_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f759,plain,
    ( ~ spl5_20
    | spl5_1
    | ~ spl5_16
    | spl5_27 ),
    inference(avatar_split_clause,[],[f724,f715,f458,f78,f555])).

fof(f458,plain,
    ( spl5_16
  <=> ! [X3,X2] :
        ( X2 = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f724,plain,
    ( sK1 = k6_relat_1(sK0)
    | ~ r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl5_16
    | spl5_27 ),
    inference(trivial_inequality_removal,[],[f719])).

fof(f719,plain,
    ( sK3(sK0,sK1) != sK3(sK0,sK1)
    | sK1 = k6_relat_1(sK0)
    | ~ r2_hidden(sK3(sK0,sK1),sK0)
    | ~ spl5_16
    | spl5_27 ),
    inference(superposition,[],[f716,f586])).

fof(f586,plain,
    ( ! [X1] :
        ( sK3(X1,sK1) = sK4(X1,sK1)
        | sK1 = k6_relat_1(X1)
        | ~ r2_hidden(sK3(X1,sK1),sK0) )
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f578])).

fof(f578,plain,
    ( ! [X1] :
        ( sK3(X1,sK1) = sK4(X1,sK1)
        | sK1 = k6_relat_1(X1)
        | sK3(X1,sK1) = sK4(X1,sK1)
        | ~ r2_hidden(sK3(X1,sK1),sK0) )
    | ~ spl5_16 ),
    inference(resolution,[],[f48,f459])).

fof(f459,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | X2 = X3
        | ~ r2_hidden(X2,sK0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f458])).

fof(f48,plain,(
    ! [X4] :
      ( r2_hidden(k4_tarski(sK3(X4,sK1),sK4(X4,sK1)),sK1)
      | sK3(X4,sK1) = sK4(X4,sK1)
      | sK1 = k6_relat_1(X4) ) ),
    inference(resolution,[],[f19,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | sK3(X0,X1) = sK4(X0,X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f716,plain,
    ( sK3(sK0,sK1) != sK4(sK0,sK1)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f715])).

fof(f558,plain,
    ( spl5_1
    | spl5_20
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f552,f82,f555,f78])).

fof(f552,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | sK1 = k6_relat_1(sK0)
    | ~ spl5_2 ),
    inference(factoring,[],[f539])).

fof(f539,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(X3,sK1),sK0)
        | sK1 = k6_relat_1(X3)
        | r2_hidden(sK3(X3,sK1),X3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f47,f202])).

fof(f202,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(k4_tarski(X5,X6),sK1)
        | r2_hidden(X5,sK0) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f57,f84])).

fof(f57,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),sK1)
      | r2_hidden(X5,k1_relat_1(sK1)) ) ),
    inference(global_subsumption,[],[f20,f49])).

fof(f49,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_1(sK1)
      | r2_hidden(X5,k1_relat_1(sK1))
      | ~ r2_hidden(k4_tarski(X5,X6),sK1) ) ),
    inference(resolution,[],[f19,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f47,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK3(X3,sK1),sK4(X3,sK1)),sK1)
      | r2_hidden(sK3(X3,sK1),X3)
      | sK1 = k6_relat_1(X3) ) ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK3(X0,X1),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f460,plain,
    ( ~ spl5_8
    | ~ spl5_4
    | spl5_16
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f272,f110,f458,f158,f357])).

fof(f357,plain,
    ( spl5_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f272,plain,
    ( ! [X2,X3] :
        ( X2 = X3
        | ~ r2_hidden(X2,sK0)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(k4_tarski(X2,X3),sK1) )
    | ~ spl5_3 ),
    inference(superposition,[],[f111,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f366,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f20,f357])).

fof(f255,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f205,f238])).

fof(f238,plain,
    ( sK2 = k1_funct_1(sK1,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f58,f164])).

fof(f164,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl5_5
  <=> r2_hidden(k4_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f58,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(k4_tarski(X7,X8),sK1)
      | k1_funct_1(sK1,X7) = X8 ) ),
    inference(global_subsumption,[],[f20,f50])).

fof(f50,plain,(
    ! [X8,X7] :
      ( ~ v1_funct_1(sK1)
      | k1_funct_1(sK1,X7) = X8
      | ~ r2_hidden(k4_tarski(X7,X8),sK1) ) ),
    inference(resolution,[],[f19,f35])).

fof(f205,plain,
    ( sK2 != k1_funct_1(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f204])).

fof(f204,plain,
    ( sK0 != sK0
    | sK2 != k1_funct_1(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f169,f84])).

fof(f169,plain,
    ( sK0 != k1_relat_1(sK1)
    | sK2 != k1_funct_1(sK1,sK2)
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f168])).

fof(f168,plain,
    ( sK1 != sK1
    | sK0 != k1_relat_1(sK1)
    | sK2 != k1_funct_1(sK1,sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f17,f80])).

fof(f80,plain,
    ( sK1 = k6_relat_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f17,plain,
    ( sK0 != k1_relat_1(sK1)
    | sK2 != k1_funct_1(sK1,sK2)
    | sK1 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f186,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f83,f119])).

fof(f119,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(superposition,[],[f22,f80])).

fof(f22,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f83,plain,
    ( sK0 != k1_relat_1(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f172,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f19,f158])).

fof(f165,plain,
    ( ~ spl5_4
    | spl5_5
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f136,f82,f78,f162,f158])).

fof(f136,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f135,f80])).

fof(f135,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK2,sK2),k6_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f134,f80])).

fof(f134,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | r2_hidden(k4_tarski(sK2,sK2),k6_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f133,f41])).

fof(f41,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | X2 != X3
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f133,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f132])).

fof(f132,plain,
    ( sK1 != sK1
    | r2_hidden(sK2,sK0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f114,f80])).

fof(f114,plain,
    ( r2_hidden(sK2,sK0)
    | sK1 != k6_relat_1(sK0)
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( sK0 != sK0
    | r2_hidden(sK2,sK0)
    | sK1 != k6_relat_1(sK0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f16,f84])).

fof(f16,plain,
    ( sK0 != k1_relat_1(sK1)
    | r2_hidden(sK2,sK0)
    | sK1 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f112,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f15,f110,f78])).

fof(f15,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_funct_1(sK1,X2) = X2
      | sK1 = k6_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f18,f82,f78])).

fof(f18,plain,
    ( sK0 = k1_relat_1(sK1)
    | sK1 = k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
