%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0639+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 613 expanded)
%              Number of leaves         :   20 ( 196 expanded)
%              Depth                    :   20
%              Number of atoms          :  664 (3987 expanded)
%              Number of equality atoms :   74 ( 270 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f633,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f79,f85,f116,f223,f231,f332,f344,f390,f401,f417,f632])).

fof(f632,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_26
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f631])).

fof(f631,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_26
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f630,f59])).

fof(f59,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_1
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f630,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_26
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f629,f63])).

fof(f63,plain,
    ( v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_2
  <=> v1_funct_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f629,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_26
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f628,f35])).

fof(f35,plain,(
    ~ v2_funct_1(k5_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v2_funct_1(k5_relat_1(sK0,sK1))
    & v2_funct_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_funct_1(k5_relat_1(X0,X1))
            & v2_funct_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(sK0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ v2_funct_1(k5_relat_1(sK0,X1))
        & v2_funct_1(X1)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(k5_relat_1(sK0,sK1))
      & v2_funct_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(k5_relat_1(X0,X1))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( v2_funct_1(X1)
                & v2_funct_1(X0) )
             => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

fof(f628,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_26
    | ~ spl4_30 ),
    inference(trivial_inequality_removal,[],[f627])).

fof(f627,plain,
    ( sK2(k5_relat_1(sK0,sK1)) != sK2(k5_relat_1(sK0,sK1))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_26
    | ~ spl4_30 ),
    inference(superposition,[],[f43,f611])).

fof(f611,plain,
    ( sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1))
    | ~ spl4_26
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f610,f356])).

fof(f356,plain,
    ( r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl4_26
  <=> r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f610,plain,
    ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | sK2(k5_relat_1(sK0,sK1)) = sK3(k5_relat_1(sK0,sK1))
    | ~ spl4_30 ),
    inference(equality_resolution,[],[f385])).

fof(f385,plain,
    ( ! [X2] :
        ( k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | ~ r2_hidden(X2,k1_relat_1(sK0))
        | sK3(k5_relat_1(sK0,sK1)) = X2 )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl4_30
  <=> ! [X2] :
        ( k1_funct_1(sK0,X2) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | ~ r2_hidden(X2,k1_relat_1(sK0))
        | sK3(k5_relat_1(sK0,sK1)) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f43,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK2(X0) != sK3(X0)
            & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK2(X0) != sK3(X0)
        & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f417,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_28 ),
    inference(subsumption_resolution,[],[f415,f59])).

fof(f415,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_2
    | spl4_28 ),
    inference(subsumption_resolution,[],[f414,f63])).

fof(f414,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_28 ),
    inference(subsumption_resolution,[],[f413,f35])).

fof(f413,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_28 ),
    inference(subsumption_resolution,[],[f412,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f412,plain,
    ( ~ v1_relat_1(sK1)
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_28 ),
    inference(subsumption_resolution,[],[f406,f32])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f406,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_28 ),
    inference(resolution,[],[f391,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,X0)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl4_28 ),
    inference(resolution,[],[f375,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(sK0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK0,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f48,f29])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK0,X1)))
      | r2_hidden(X0,k1_relat_1(sK0))
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f30,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f375,plain,
    ( ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl4_28
  <=> r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f401,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_26 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_26 ),
    inference(subsumption_resolution,[],[f399,f59])).

fof(f399,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_2
    | spl4_26 ),
    inference(subsumption_resolution,[],[f398,f63])).

fof(f398,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_26 ),
    inference(subsumption_resolution,[],[f397,f35])).

fof(f397,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_26 ),
    inference(subsumption_resolution,[],[f396,f31])).

fof(f396,plain,
    ( ~ v1_relat_1(sK1)
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_26 ),
    inference(subsumption_resolution,[],[f393,f32])).

fof(f393,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_26 ),
    inference(resolution,[],[f363,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,X0)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl4_26 ),
    inference(resolution,[],[f357,f50])).

fof(f357,plain,
    ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f355])).

fof(f390,plain,
    ( ~ spl4_28
    | spl4_30
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f389,f325,f384,f373])).

fof(f325,plain,
    ( spl4_24
  <=> k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f389,plain,
    ( ! [X3] :
        ( k1_funct_1(sK0,X3) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) )
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f388,f29])).

fof(f388,plain,
    ( ! [X3] :
        ( k1_funct_1(sK0,X3) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f387,f30])).

fof(f387,plain,
    ( ! [X3] :
        ( k1_funct_1(sK0,X3) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f367,f33])).

fof(f33,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f367,plain,
    ( ! [X3] :
        ( k1_funct_1(sK0,X3) != k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
        | sK3(k5_relat_1(sK0,sK1)) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
        | ~ v2_funct_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl4_24 ),
    inference(superposition,[],[f39,f327])).

fof(f327,plain,
    ( k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f325])).

fof(f39,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f344,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_25 ),
    inference(subsumption_resolution,[],[f342,f59])).

fof(f342,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_2
    | spl4_25 ),
    inference(subsumption_resolution,[],[f341,f63])).

fof(f341,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_25 ),
    inference(subsumption_resolution,[],[f340,f35])).

fof(f340,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_25 ),
    inference(resolution,[],[f338,f40])).

fof(f338,plain,
    ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl4_25 ),
    inference(subsumption_resolution,[],[f337,f31])).

fof(f337,plain,
    ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(sK1)
    | spl4_25 ),
    inference(subsumption_resolution,[],[f336,f32])).

fof(f336,plain,
    ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_25 ),
    inference(subsumption_resolution,[],[f335,f29])).

fof(f335,plain,
    ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_25 ),
    inference(subsumption_resolution,[],[f334,f30])).

fof(f334,plain,
    ( ~ r2_hidden(sK2(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_25 ),
    inference(resolution,[],[f331,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f331,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl4_25
  <=> r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f332,plain,
    ( spl4_24
    | ~ spl4_25
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f323,f217,f329,f325])).

fof(f217,plain,
    ( spl4_14
  <=> ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f323,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))
    | ~ spl4_14 ),
    inference(equality_resolution,[],[f218])).

fof(f218,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X2 )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f217])).

fof(f231,plain,
    ( ~ spl4_4
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f229,f31])).

fof(f229,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f228,f32])).

fof(f228,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f227,f29])).

fof(f227,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f226,f30])).

fof(f226,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f225,f106])).

fof(f106,plain,
    ( r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_4
  <=> r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f225,plain,
    ( ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_12 ),
    inference(resolution,[],[f208,f46])).

fof(f208,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl4_12
  <=> r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f223,plain,
    ( ~ spl4_12
    | spl4_14
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f222,f105,f66,f62,f58,f217,f206])).

fof(f66,plain,
    ( spl4_3
  <=> k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f222,plain,
    ( ! [X3] :
        ( k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) != k1_funct_1(sK1,X3)
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f221,f31])).

fof(f221,plain,
    ( ! [X3] :
        ( k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) != k1_funct_1(sK1,X3)
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f220,f32])).

fof(f220,plain,
    ( ! [X3] :
        ( k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) != k1_funct_1(sK1,X3)
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f200,f34])).

fof(f34,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f200,plain,
    ( ! [X3] :
        ( k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1)))) != k1_funct_1(sK1,X3)
        | k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))) = X3
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(superposition,[],[f39,f191])).

fof(f191,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1)))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f185,f190])).

fof(f190,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f189,f59])).

fof(f189,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f188,f63])).

fof(f188,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f183,f35])).

fof(f183,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK2(k5_relat_1(sK0,sK1))))
    | v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f127,f40])).

fof(f127,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_relat_1(k5_relat_1(sK0,sK1)))
      | k1_funct_1(k5_relat_1(sK0,sK1),X5) = k1_funct_1(sK1,k1_funct_1(sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f123,f31])).

fof(f123,plain,(
    ! [X5] :
      ( k1_funct_1(k5_relat_1(sK0,sK1),X5) = k1_funct_1(sK1,k1_funct_1(sK0,X5))
      | ~ r2_hidden(X5,k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f51,f32])).

fof(f51,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X3)
      | k1_funct_1(k5_relat_1(sK0,X3),X2) = k1_funct_1(X3,k1_funct_1(sK0,X2))
      | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(sK0,X3)))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f49,f29])).

fof(f49,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(sK0,X3)))
      | k1_funct_1(k5_relat_1(sK0,X3),X2) = k1_funct_1(X3,k1_funct_1(sK0,X2))
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f30,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f185,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f68,f180])).

fof(f180,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1))) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(k5_relat_1(sK0,sK1))))
    | ~ spl4_4 ),
    inference(resolution,[],[f127,f106])).

fof(f68,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f116,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f114,f59])).

fof(f114,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f113,f63])).

fof(f113,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f112,f35])).

fof(f112,plain,
    ( v2_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_4 ),
    inference(resolution,[],[f107,f41])).

fof(f107,plain,
    ( ~ r2_hidden(sK3(k5_relat_1(sK0,sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f85,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f83,f29])).

fof(f83,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f82,f30])).

fof(f82,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f81,f31])).

fof(f81,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f80,f32])).

fof(f80,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl4_2 ),
    inference(resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f64,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f79,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f77,f29])).

fof(f77,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f71,f31])).

fof(f71,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl4_1 ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f60,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f69,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f56,f66,f62,f58])).

fof(f56,plain,
    ( k1_funct_1(k5_relat_1(sK0,sK1),sK2(k5_relat_1(sK0,sK1))) = k1_funct_1(k5_relat_1(sK0,sK1),sK3(k5_relat_1(sK0,sK1)))
    | ~ v1_funct_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f35,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
