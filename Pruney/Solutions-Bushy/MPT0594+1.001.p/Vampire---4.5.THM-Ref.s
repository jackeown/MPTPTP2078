%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0594+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:16 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 110 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  160 ( 415 expanded)
%              Number of equality atoms :   47 ( 150 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f31,f36,f41,f45,f57,f61,f87,f103,f108])).

fof(f108,plain,
    ( ~ spl3_3
    | ~ spl3_9
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_9
    | spl3_16 ),
    inference(subsumption_resolution,[],[f104,f102])).

fof(f102,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK0)) != k10_relat_1(sK2,k1_relat_1(sK0))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_16
  <=> k1_relat_1(k5_relat_1(sK2,sK0)) = k10_relat_1(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f104,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK0)) = k10_relat_1(sK2,k1_relat_1(sK0))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f60,f30])).

fof(f30,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f60,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(X2)
        | k1_relat_1(k5_relat_1(X2,sK0)) = k10_relat_1(X2,k1_relat_1(sK0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_9
  <=> ! [X2] :
        ( k1_relat_1(k5_relat_1(X2,sK0)) = k10_relat_1(X2,k1_relat_1(sK0))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f103,plain,
    ( ~ spl3_16
    | spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f98,f84,f18,f100])).

fof(f18,plain,
    ( spl3_1
  <=> k1_relat_1(k5_relat_1(sK2,sK0)) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f84,plain,
    ( spl3_13
  <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f98,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK0)) != k10_relat_1(sK2,k1_relat_1(sK0))
    | spl3_1
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f20,f86])).

fof(f86,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f20,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f87,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f80,f55,f28,f84])).

fof(f55,plain,
    ( spl3_8
  <=> ! [X1] :
        ( k1_relat_1(k5_relat_1(X1,sK1)) = k10_relat_1(X1,k1_relat_1(sK0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f80,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK0))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f56,f30])).

fof(f56,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X1,sK1)) = k10_relat_1(X1,k1_relat_1(sK0)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f61,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f48,f43,f38,f59])).

fof(f38,plain,
    ( spl3_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f43,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f48,plain,
    ( ! [X2] :
        ( k1_relat_1(k5_relat_1(X2,sK0)) = k10_relat_1(X2,k1_relat_1(sK0))
        | ~ v1_relat_1(X2) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f57,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f53,f43,f33,f23,f55])).

fof(f23,plain,
    ( spl3_2
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f33,plain,
    ( spl3_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f53,plain,
    ( ! [X1] :
        ( k1_relat_1(k5_relat_1(X1,sK1)) = k10_relat_1(X1,k1_relat_1(sK0))
        | ~ v1_relat_1(X1) )
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f47,f25])).

fof(f25,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f47,plain,
    ( ! [X1] :
        ( k1_relat_1(k5_relat_1(X1,sK1)) = k10_relat_1(X1,k1_relat_1(sK1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f45,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f16,f43])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f41,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f11,f38])).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1))
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f9,f8,f7])).

fof(f7,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1))
                & k1_relat_1(X1) = k1_relat_1(X0)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(k5_relat_1(X2,sK0))
              & k1_relat_1(X1) = k1_relat_1(sK0)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(k5_relat_1(X2,sK0))
            & k1_relat_1(X1) = k1_relat_1(sK0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k1_relat_1(k5_relat_1(X2,sK0)) != k1_relat_1(k5_relat_1(X2,sK1))
          & k1_relat_1(sK0) = k1_relat_1(sK1)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X2] :
        ( k1_relat_1(k5_relat_1(X2,sK0)) != k1_relat_1(k5_relat_1(X2,sK1))
        & k1_relat_1(sK0) = k1_relat_1(sK1)
        & v1_relat_1(X2) )
   => ( k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1))
      & k1_relat_1(sK0) = k1_relat_1(sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1))
              & k1_relat_1(X1) = k1_relat_1(X0)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) != k1_relat_1(k5_relat_1(X2,X1))
              & k1_relat_1(X1) = k1_relat_1(X0)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( k1_relat_1(X1) = k1_relat_1(X0)
                 => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X1) = k1_relat_1(X0)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(f36,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f12,f33])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f28])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f23])).

fof(f14,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f18])).

fof(f15,plain,(
    k1_relat_1(k5_relat_1(sK2,sK0)) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
