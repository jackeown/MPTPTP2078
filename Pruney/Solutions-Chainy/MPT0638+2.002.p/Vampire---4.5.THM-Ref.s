%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 236 expanded)
%              Number of leaves         :   26 (  89 expanded)
%              Depth                    :   17
%              Number of atoms          :  495 (1104 expanded)
%              Number of equality atoms :  110 ( 364 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f608,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f98,f103,f109,f116,f236,f277,f293,f607])).

fof(f607,plain,
    ( ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | spl10_17
    | ~ spl10_21 ),
    inference(avatar_contradiction_clause,[],[f606])).

fof(f606,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | spl10_17
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f605,f287])).

fof(f287,plain,
    ( sP0(sK9(sK6,k2_relat_1(sK5)),sK5)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl10_21
  <=> sP0(sK9(sK6,k2_relat_1(sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f605,plain,
    ( ~ sP0(sK9(sK6,k2_relat_1(sK5)),sK5)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | spl10_17 ),
    inference(forward_demodulation,[],[f604,f82])).

fof(f82,plain,
    ( k2_relat_1(sK5) = k1_relat_1(sK6)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl10_3
  <=> k2_relat_1(sK5) = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f604,plain,
    ( ~ sP0(sK9(sK6,k1_relat_1(sK6)),sK5)
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | spl10_17 ),
    inference(subsumption_resolution,[],[f597,f239])).

fof(f239,plain,
    ( ! [X0] : ~ sP3(sK6,X0)
    | ~ spl10_3
    | spl10_17 ),
    inference(duplicate_literal_removal,[],[f237])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ sP3(sK6,X0)
        | ~ sP3(sK6,X0) )
    | ~ spl10_3
    | spl10_17 ),
    inference(superposition,[],[f235,f134])).

fof(f134,plain,
    ( ! [X0] :
        ( k2_relat_1(sK5) = X0
        | ~ sP3(sK6,X0) )
    | ~ spl10_3 ),
    inference(superposition,[],[f58,f82])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( sK9(X0,X1) != k1_funct_1(X0,sK9(X0,X1))
          & r2_hidden(sK9(X0,X1),X1) )
        | k1_relat_1(X0) != X1 )
      & ( ( ! [X3] :
              ( k1_funct_1(X0,X3) = X3
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X0) = X1 )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != X2
          & r2_hidden(X2,X1) )
     => ( sK9(X0,X1) != k1_funct_1(X0,sK9(X0,X1))
        & r2_hidden(sK9(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( k1_funct_1(X0,X2) != X2
            & r2_hidden(X2,X1) )
        | k1_relat_1(X0) != X1 )
      & ( ( ! [X3] :
              ( k1_funct_1(X0,X3) = X3
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X0) = X1 )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( sP3(X1,X0)
        | ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | ~ sP3(X1,X0) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( sP3(X1,X0)
        | ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | ~ sP3(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( sP3(X1,X0)
    <=> ( ! [X2] :
            ( k1_funct_1(X1,X2) = X2
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f235,plain,
    ( ~ sP3(sK6,k2_relat_1(sK5))
    | spl10_17 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl10_17
  <=> sP3(sK6,k2_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f597,plain,
    ( sP3(sK6,k1_relat_1(sK6))
    | ~ sP0(sK9(sK6,k1_relat_1(sK6)),sK5)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(trivial_inequality_removal,[],[f596])).

fof(f596,plain,
    ( sK9(sK6,k1_relat_1(sK6)) != sK9(sK6,k1_relat_1(sK6))
    | sP3(sK6,k1_relat_1(sK6))
    | ~ sP0(sK9(sK6,k1_relat_1(sK6)),sK5)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(superposition,[],[f67,f560])).

fof(f560,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,X0) = X0
        | ~ sP0(X0,sK5) )
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f549,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK8(X0,X1)) = X0
          & r2_hidden(sK8(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK8(X0,X1)) = X0
        & r2_hidden(sK8(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f549,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,X0) = X0
        | ~ r2_hidden(sK8(X0,sK5),k1_relat_1(sK5))
        | ~ sP0(X0,sK5) )
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(superposition,[],[f509,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK8(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f509,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK5)) )
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f508,f92])).

fof(f92,plain,
    ( v1_relat_1(sK6)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl10_5
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f508,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK5))
        | ~ v1_relat_1(sK6) )
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f507,f87])).

fof(f87,plain,
    ( v1_funct_1(sK6)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl10_4
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f507,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK5))
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f506,f102])).

fof(f102,plain,
    ( v1_relat_1(sK5)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl10_7
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f506,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK5))
        | ~ v1_relat_1(sK5)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f498,f97])).

fof(f97,plain,
    ( v1_funct_1(sK5)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl10_6
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f498,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK5))
        | ~ v1_funct_1(sK5)
        | ~ v1_relat_1(sK5)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl10_2 ),
    inference(superposition,[],[f63,f77])).

fof(f77,plain,
    ( sK5 = k5_relat_1(sK5,sK6)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl10_2
  <=> sK5 = k5_relat_1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f67,plain,(
    ! [X0] :
      ( sK9(X0,k1_relat_1(X0)) != k1_funct_1(X0,sK9(X0,k1_relat_1(X0)))
      | sP3(X0,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | sK9(X0,X1) != k1_funct_1(X0,sK9(X0,X1))
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f293,plain,
    ( spl10_21
    | ~ spl10_9
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f292,f272,f113,f285])).

fof(f113,plain,
    ( spl10_9
  <=> sP2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f272,plain,
    ( spl10_20
  <=> r2_hidden(sK9(sK6,k2_relat_1(sK5)),k2_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f292,plain,
    ( sP0(sK9(sK6,k2_relat_1(sK5)),sK5)
    | ~ spl10_9
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f282,f115])).

fof(f115,plain,
    ( sP2(sK5)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f282,plain,
    ( sP0(sK9(sK6,k2_relat_1(sK5)),sK5)
    | ~ sP2(sK5)
    | ~ spl10_20 ),
    inference(resolution,[],[f274,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | sP0(X0,X1)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f48,f64])).

fof(f64,plain,(
    ! [X0] :
      ( sP1(X0,k2_relat_1(X0))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP0(X3,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK7(X0,X1),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sP0(sK7(X0,X1),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK7(X0,X1),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sP0(sK7(X0,X1),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X2,X0) )
            & ( sP0(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f274,plain,
    ( r2_hidden(sK9(sK6,k2_relat_1(sK5)),k2_relat_1(sK5))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f272])).

fof(f277,plain,
    ( spl10_20
    | ~ spl10_3
    | spl10_17 ),
    inference(avatar_split_clause,[],[f276,f233,f80,f272])).

fof(f276,plain,
    ( r2_hidden(sK9(sK6,k2_relat_1(sK5)),k2_relat_1(sK5))
    | ~ spl10_3
    | spl10_17 ),
    inference(subsumption_resolution,[],[f268,f239])).

fof(f268,plain,
    ( r2_hidden(sK9(sK6,k2_relat_1(sK5)),k2_relat_1(sK5))
    | sP3(sK6,k2_relat_1(sK5))
    | ~ spl10_3 ),
    inference(superposition,[],[f68,f82])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0,k1_relat_1(X0)),k1_relat_1(X0))
      | sP3(X0,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | r2_hidden(sK9(X0,X1),X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f236,plain,
    ( ~ spl10_17
    | ~ spl10_4
    | ~ spl10_5
    | spl10_8 ),
    inference(avatar_split_clause,[],[f225,f106,f90,f85,f233])).

fof(f106,plain,
    ( spl10_8
  <=> sK6 = k6_relat_1(k2_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f225,plain,
    ( ~ sP3(sK6,k2_relat_1(sK5))
    | ~ spl10_4
    | ~ spl10_5
    | spl10_8 ),
    inference(unit_resulting_resolution,[],[f141,f108,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | ~ sP3(X1,X0)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ~ sP3(X1,X0) )
        & ( sP3(X1,X0)
          | k6_relat_1(X0) != X1 ) )
      | ~ sP4(X0,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> sP3(X1,X0) )
      | ~ sP4(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f108,plain,
    ( sK6 != k6_relat_1(k2_relat_1(sK5))
    | spl10_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f141,plain,
    ( ! [X0] : sP4(X0,sK6)
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f92,f87,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f11,f19,f18])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f116,plain,
    ( spl10_9
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f111,f100,f95,f113])).

fof(f111,plain,
    ( sP2(sK5)
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f102,f97,f55])).

fof(f55,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f9,f16,f15,f14])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f109,plain,
    ( ~ spl10_8
    | spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f104,f80,f70,f106])).

% (17847)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f70,plain,
    ( spl10_1
  <=> sK6 = k6_relat_1(k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f104,plain,
    ( sK6 != k6_relat_1(k2_relat_1(sK5))
    | spl10_1
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f72,f82])).

fof(f72,plain,
    ( sK6 != k6_relat_1(k1_relat_1(sK6))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f103,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f39,f100])).

fof(f39,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK6 != k6_relat_1(k1_relat_1(sK6))
    & sK5 = k5_relat_1(sK5,sK6)
    & k2_relat_1(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f7,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X1)) != X1
            & k5_relat_1(X0,X1) = X0
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & sK5 = k5_relat_1(sK5,X1)
          & k1_relat_1(X1) = k2_relat_1(sK5)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( k6_relat_1(k1_relat_1(X1)) != X1
        & sK5 = k5_relat_1(sK5,X1)
        & k1_relat_1(X1) = k2_relat_1(sK5)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK6 != k6_relat_1(k1_relat_1(sK6))
      & sK5 = k5_relat_1(sK5,sK6)
      & k2_relat_1(sK5) = k1_relat_1(sK6)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f98,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f40,f95])).

fof(f40,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f93,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f41,f90])).

fof(f41,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f42,f85])).

fof(f42,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f43,f80])).

fof(f43,plain,(
    k2_relat_1(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f44,f75])).

fof(f44,plain,(
    sK5 = k5_relat_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f45,f70])).

fof(f45,plain,(
    sK6 != k6_relat_1(k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (17865)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.43  % (17865)Refutation not found, incomplete strategy% (17865)------------------------------
% 0.20/0.43  % (17865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (17865)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.43  
% 0.20/0.43  % (17865)Memory used [KB]: 10618
% 0.20/0.43  % (17865)Time elapsed: 0.029 s
% 0.20/0.43  % (17865)------------------------------
% 0.20/0.43  % (17865)------------------------------
% 0.20/0.47  % (17861)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (17861)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f608,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f98,f103,f109,f116,f236,f277,f293,f607])).
% 0.20/0.48  fof(f607,plain,(
% 0.20/0.48    ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | spl10_17 | ~spl10_21),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f606])).
% 0.20/0.48  fof(f606,plain,(
% 0.20/0.48    $false | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | spl10_17 | ~spl10_21)),
% 0.20/0.48    inference(subsumption_resolution,[],[f605,f287])).
% 0.20/0.48  fof(f287,plain,(
% 0.20/0.48    sP0(sK9(sK6,k2_relat_1(sK5)),sK5) | ~spl10_21),
% 0.20/0.48    inference(avatar_component_clause,[],[f285])).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    spl10_21 <=> sP0(sK9(sK6,k2_relat_1(sK5)),sK5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.20/0.48  fof(f605,plain,(
% 0.20/0.48    ~sP0(sK9(sK6,k2_relat_1(sK5)),sK5) | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | spl10_17)),
% 0.20/0.48    inference(forward_demodulation,[],[f604,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    k2_relat_1(sK5) = k1_relat_1(sK6) | ~spl10_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl10_3 <=> k2_relat_1(sK5) = k1_relat_1(sK6)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.48  fof(f604,plain,(
% 0.20/0.48    ~sP0(sK9(sK6,k1_relat_1(sK6)),sK5) | (~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | spl10_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f597,f239])).
% 0.20/0.48  fof(f239,plain,(
% 0.20/0.48    ( ! [X0] : (~sP3(sK6,X0)) ) | (~spl10_3 | spl10_17)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f237])).
% 0.20/0.48  fof(f237,plain,(
% 0.20/0.48    ( ! [X0] : (~sP3(sK6,X0) | ~sP3(sK6,X0)) ) | (~spl10_3 | spl10_17)),
% 0.20/0.48    inference(superposition,[],[f235,f134])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ( ! [X0] : (k2_relat_1(sK5) = X0 | ~sP3(sK6,X0)) ) | ~spl10_3),
% 0.20/0.48    inference(superposition,[],[f58,f82])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | ~sP3(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP3(X0,X1) | (sK9(X0,X1) != k1_funct_1(X0,sK9(X0,X1)) & r2_hidden(sK9(X0,X1),X1)) | k1_relat_1(X0) != X1) & ((! [X3] : (k1_funct_1(X0,X3) = X3 | ~r2_hidden(X3,X1)) & k1_relat_1(X0) = X1) | ~sP3(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f36,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != X2 & r2_hidden(X2,X1)) => (sK9(X0,X1) != k1_funct_1(X0,sK9(X0,X1)) & r2_hidden(sK9(X0,X1),X1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != X2 & r2_hidden(X2,X1)) | k1_relat_1(X0) != X1) & ((! [X3] : (k1_funct_1(X0,X3) = X3 | ~r2_hidden(X3,X1)) & k1_relat_1(X0) = X1) | ~sP3(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X1,X0] : ((sP3(X1,X0) | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | ~sP3(X1,X0)))),
% 0.20/0.48    inference(flattening,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X1,X0] : ((sP3(X1,X0) | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | ~sP3(X1,X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X1,X0] : (sP3(X1,X0) <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.48  fof(f235,plain,(
% 0.20/0.48    ~sP3(sK6,k2_relat_1(sK5)) | spl10_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f233])).
% 0.20/0.48  fof(f233,plain,(
% 0.20/0.48    spl10_17 <=> sP3(sK6,k2_relat_1(sK5))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.20/0.48  fof(f597,plain,(
% 0.20/0.48    sP3(sK6,k1_relat_1(sK6)) | ~sP0(sK9(sK6,k1_relat_1(sK6)),sK5) | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f596])).
% 0.20/0.48  fof(f596,plain,(
% 0.20/0.48    sK9(sK6,k1_relat_1(sK6)) != sK9(sK6,k1_relat_1(sK6)) | sP3(sK6,k1_relat_1(sK6)) | ~sP0(sK9(sK6,k1_relat_1(sK6)),sK5) | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 0.20/0.48    inference(superposition,[],[f67,f560])).
% 0.20/0.48  fof(f560,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK6,X0) = X0 | ~sP0(X0,sK5)) ) | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f549,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),k1_relat_1(X1)) | ~sP0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK8(X0,X1)) = X0 & r2_hidden(sK8(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK8(X0,X1)) = X0 & r2_hidden(sK8(X0,X1),k1_relat_1(X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f549,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK6,X0) = X0 | ~r2_hidden(sK8(X0,sK5),k1_relat_1(sK5)) | ~sP0(X0,sK5)) ) | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 0.20/0.48    inference(superposition,[],[f509,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_funct_1(X1,sK8(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f509,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK5,X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) | ~r2_hidden(X0,k1_relat_1(sK5))) ) | (~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f508,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    v1_relat_1(sK6) | ~spl10_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f90])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl10_5 <=> v1_relat_1(sK6)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.48  fof(f508,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK5,X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) | ~r2_hidden(X0,k1_relat_1(sK5)) | ~v1_relat_1(sK6)) ) | (~spl10_2 | ~spl10_4 | ~spl10_6 | ~spl10_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f507,f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    v1_funct_1(sK6) | ~spl10_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f85])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl10_4 <=> v1_funct_1(sK6)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.48  fof(f507,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK5,X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) | ~r2_hidden(X0,k1_relat_1(sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) ) | (~spl10_2 | ~spl10_6 | ~spl10_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f506,f102])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    v1_relat_1(sK5) | ~spl10_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f100])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl10_7 <=> v1_relat_1(sK5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.48  fof(f506,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK5,X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) | ~r2_hidden(X0,k1_relat_1(sK5)) | ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) ) | (~spl10_2 | ~spl10_6)),
% 0.20/0.48    inference(subsumption_resolution,[],[f498,f97])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    v1_funct_1(sK5) | ~spl10_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f95])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl10_6 <=> v1_funct_1(sK5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.48  fof(f498,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK5,X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) | ~r2_hidden(X0,k1_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) ) | ~spl10_2),
% 0.20/0.48    inference(superposition,[],[f63,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    sK5 = k5_relat_1(sK5,sK6) | ~spl10_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl10_2 <=> sK5 = k5_relat_1(sK5,sK6)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X0] : (sK9(X0,k1_relat_1(X0)) != k1_funct_1(X0,sK9(X0,k1_relat_1(X0))) | sP3(X0,k1_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP3(X0,X1) | sK9(X0,X1) != k1_funct_1(X0,sK9(X0,X1)) | k1_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f293,plain,(
% 0.20/0.48    spl10_21 | ~spl10_9 | ~spl10_20),
% 0.20/0.48    inference(avatar_split_clause,[],[f292,f272,f113,f285])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    spl10_9 <=> sP2(sK5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.48  fof(f272,plain,(
% 0.20/0.48    spl10_20 <=> r2_hidden(sK9(sK6,k2_relat_1(sK5)),k2_relat_1(sK5))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.20/0.48  fof(f292,plain,(
% 0.20/0.48    sP0(sK9(sK6,k2_relat_1(sK5)),sK5) | (~spl10_9 | ~spl10_20)),
% 0.20/0.48    inference(subsumption_resolution,[],[f282,f115])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    sP2(sK5) | ~spl10_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f113])).
% 0.20/0.48  fof(f282,plain,(
% 0.20/0.48    sP0(sK9(sK6,k2_relat_1(sK5)),sK5) | ~sP2(sK5) | ~spl10_20),
% 0.20/0.48    inference(resolution,[],[f274,f158])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | sP0(X0,X1) | ~sP2(X1)) )),
% 0.20/0.48    inference(resolution,[],[f48,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0] : (sP1(X0,k2_relat_1(X0)) | ~sP2(X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP1(X0,X1) | k2_relat_1(X0) != X1 | ~sP2(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~r2_hidden(X3,X1) | sP0(X3,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (sP0(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (sP0(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.48  fof(f274,plain,(
% 0.20/0.48    r2_hidden(sK9(sK6,k2_relat_1(sK5)),k2_relat_1(sK5)) | ~spl10_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f272])).
% 0.20/0.48  fof(f277,plain,(
% 0.20/0.48    spl10_20 | ~spl10_3 | spl10_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f276,f233,f80,f272])).
% 0.20/0.48  fof(f276,plain,(
% 0.20/0.48    r2_hidden(sK9(sK6,k2_relat_1(sK5)),k2_relat_1(sK5)) | (~spl10_3 | spl10_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f268,f239])).
% 0.20/0.48  fof(f268,plain,(
% 0.20/0.48    r2_hidden(sK9(sK6,k2_relat_1(sK5)),k2_relat_1(sK5)) | sP3(sK6,k2_relat_1(sK5)) | ~spl10_3),
% 0.20/0.48    inference(superposition,[],[f68,f82])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK9(X0,k1_relat_1(X0)),k1_relat_1(X0)) | sP3(X0,k1_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP3(X0,X1) | r2_hidden(sK9(X0,X1),X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f236,plain,(
% 0.20/0.48    ~spl10_17 | ~spl10_4 | ~spl10_5 | spl10_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f225,f106,f90,f85,f233])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl10_8 <=> sK6 = k6_relat_1(k2_relat_1(sK5))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    ~sP3(sK6,k2_relat_1(sK5)) | (~spl10_4 | ~spl10_5 | spl10_8)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f141,f108,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | ~sP3(X1,X0) | ~sP4(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ~sP3(X1,X0)) & (sP3(X1,X0) | k6_relat_1(X0) != X1)) | ~sP4(X0,X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> sP3(X1,X0)) | ~sP4(X0,X1))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    sK6 != k6_relat_1(k2_relat_1(sK5)) | spl10_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f106])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ( ! [X0] : (sP4(X0,sK6)) ) | (~spl10_4 | ~spl10_5)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f92,f87,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP4(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : (sP4(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(definition_folding,[],[f11,f19,f18])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    spl10_9 | ~spl10_6 | ~spl10_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f111,f100,f95,f113])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    sP2(sK5) | (~spl10_6 | ~spl10_7)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f102,f97,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(definition_folding,[],[f9,f16,f15,f14])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ~spl10_8 | spl10_1 | ~spl10_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f104,f80,f70,f106])).
% 0.20/0.48  % (17847)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl10_1 <=> sK6 = k6_relat_1(k1_relat_1(sK6))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    sK6 != k6_relat_1(k2_relat_1(sK5)) | (spl10_1 | ~spl10_3)),
% 0.20/0.48    inference(forward_demodulation,[],[f72,f82])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    sK6 != k6_relat_1(k1_relat_1(sK6)) | spl10_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f70])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl10_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f100])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v1_relat_1(sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    (sK6 != k6_relat_1(k1_relat_1(sK6)) & sK5 = k5_relat_1(sK5,sK6) & k2_relat_1(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f7,f22,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & sK5 = k5_relat_1(sK5,X1) & k1_relat_1(X1) = k2_relat_1(sK5) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & sK5 = k5_relat_1(sK5,X1) & k1_relat_1(X1) = k2_relat_1(sK5) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK6 != k6_relat_1(k1_relat_1(sK6)) & sK5 = k5_relat_1(sK5,sK6) & k2_relat_1(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl10_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f95])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    v1_funct_1(sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    spl10_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f90])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    v1_relat_1(sK6)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    spl10_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f42,f85])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    v1_funct_1(sK6)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl10_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f43,f80])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    k2_relat_1(sK5) = k1_relat_1(sK6)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl10_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f44,f75])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    sK5 = k5_relat_1(sK5,sK6)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ~spl10_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f45,f70])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    sK6 != k6_relat_1(k1_relat_1(sK6))),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (17861)------------------------------
% 0.20/0.48  % (17861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17861)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (17861)Memory used [KB]: 11001
% 0.20/0.48  % (17861)Time elapsed: 0.064 s
% 0.20/0.48  % (17861)------------------------------
% 0.20/0.48  % (17861)------------------------------
% 0.20/0.48  % (17857)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (17844)Success in time 0.128 s
%------------------------------------------------------------------------------
