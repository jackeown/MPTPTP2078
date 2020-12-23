%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t54_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:15 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 443 expanded)
%              Number of leaves         :   11 ( 165 expanded)
%              Depth                    :   15
%              Number of atoms          :  458 (3366 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f89,f99,f111,f119,f129])).

fof(f129,plain,(
    ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f127,f16])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v2_wellord1(sK1)
    & r3_wellord1(sK0,sK1,sK2)
    & v2_wellord1(sK0)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_wellord1(X1)
                & r3_wellord1(X0,X1,X2)
                & v2_wellord1(X0)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(sK0,X1,X2)
              & v2_wellord1(sK0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ v2_wellord1(sK1)
            & r3_wellord1(X0,sK1,X2)
            & v2_wellord1(X0)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_wellord1(X1)
          & r3_wellord1(X0,X1,X2)
          & v2_wellord1(X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ~ v2_wellord1(X1)
        & r3_wellord1(X0,X1,sK2)
        & v2_wellord1(X0)
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => v2_wellord1(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => v2_wellord1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t54_wellord1.p',t54_wellord1)).

fof(f127,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f125,f20])).

fof(f20,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f125,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f123,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t54_wellord1.p',d4_wellord1)).

fof(f123,plain,
    ( ~ v1_wellord1(sK0)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f122,f16])).

fof(f122,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_wellord1(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f121,f21])).

fof(f21,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r3_wellord1(X0,sK1,sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_wellord1(X0) )
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f120,f18])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ v1_wellord1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ r3_wellord1(X0,sK1,sK2) )
    | ~ spl3_8 ),
    inference(resolution,[],[f66,f19])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_wellord1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r3_wellord1(X0,sK1,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ r3_wellord1(X0,sK1,X1)
        | ~ v1_wellord1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f119,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f117,f16])).

fof(f117,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f115,f20])).

fof(f115,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f113,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f113,plain,
    ( ~ v6_relat_2(sK0)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f112,f16])).

fof(f112,plain,
    ( ~ v6_relat_2(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f105,f21])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r3_wellord1(X0,sK1,sK2)
        | ~ v6_relat_2(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f104,f18])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r3_wellord1(X0,sK1,sK2)
        | ~ v6_relat_2(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f79,f19])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r3_wellord1(X0,sK1,X1)
        | ~ v6_relat_2(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f77,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ v6_relat_2(X0)
        | ~ r3_wellord1(X0,sK1,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v6_relat_2(X1)
      | ~ v6_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
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
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ( ( v1_wellord1(X0)
                   => v1_wellord1(X1) )
                  & ( v4_relat_2(X0)
                   => v4_relat_2(X1) )
                  & ( v6_relat_2(X0)
                   => v6_relat_2(X1) )
                  & ( v8_relat_2(X0)
                   => v8_relat_2(X1) )
                  & ( v1_relat_2(X0)
                   => v1_relat_2(X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t54_wellord1.p',t53_wellord1)).

fof(f63,plain,
    ( ~ v6_relat_2(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_7
  <=> ~ v6_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f111,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f109,f16])).

fof(f109,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f107,f20])).

fof(f107,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f103,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,
    ( ~ v4_relat_2(sK0)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f102,f16])).

fof(f102,plain,
    ( ~ v4_relat_2(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f101,f21])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r3_wellord1(X0,sK1,sK2)
        | ~ v4_relat_2(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f100,f18])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ r3_wellord1(X0,sK1,sK2)
        | ~ v4_relat_2(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f76,f19])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r3_wellord1(X0,sK1,X1)
        | ~ v4_relat_2(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f74,f17])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_2(X0)
        | ~ r3_wellord1(X0,sK1,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f57,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_2(X1)
      | ~ v4_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,
    ( ~ v4_relat_2(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_5
  <=> ~ v4_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f99,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f97,f16])).

fof(f97,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f95,f20])).

fof(f95,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f93,f24])).

fof(f24,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,
    ( ~ v8_relat_2(sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f92,f16])).

fof(f92,plain,
    ( ~ v8_relat_2(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f91,f21])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r3_wellord1(X0,sK1,sK2)
        | ~ v8_relat_2(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f90,f18])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r3_wellord1(X0,sK1,sK2)
        | ~ v8_relat_2(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f73,f19])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r3_wellord1(X0,sK1,X1)
        | ~ v8_relat_2(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f71,f17])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ v8_relat_2(X0)
        | ~ r3_wellord1(X0,sK1,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f51,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v8_relat_2(X1)
      | ~ v8_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,
    ( ~ v8_relat_2(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_3
  <=> ~ v8_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f89,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f87,f16])).

fof(f87,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f85,f20])).

fof(f85,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f83,f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,
    ( ~ v1_relat_2(sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f82,f16])).

fof(f82,plain,
    ( ~ v1_relat_2(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f81,f21])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r3_wellord1(X0,sK1,sK2)
        | ~ v1_relat_2(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f80,f18])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ r3_wellord1(X0,sK1,sK2)
        | ~ v1_relat_2(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f70,f19])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r3_wellord1(X0,sK1,X1)
        | ~ v1_relat_2(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f68,f17])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_2(X0)
        | ~ r3_wellord1(X0,sK1,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f45,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_2(X1)
      | ~ v1_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,
    ( ~ v1_relat_2(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_1
  <=> ~ v1_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f67,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f39,f65,f62,f56,f50,f44])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r3_wellord1(X0,sK1,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(sK1)
      | ~ v4_relat_2(sK1)
      | ~ v8_relat_2(sK1)
      | ~ v1_relat_2(sK1) ) ),
    inference(subsumption_resolution,[],[f38,f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r3_wellord1(X0,sK1,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(sK1)
      | ~ v4_relat_2(sK1)
      | ~ v8_relat_2(sK1)
      | ~ v1_relat_2(sK1) ) ),
    inference(resolution,[],[f37,f22])).

fof(f22,plain,(
    ~ v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_wellord1(X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v8_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_wellord1(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | v2_wellord1(X1)
      | ~ v6_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v8_relat_2(X1)
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f33,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_wellord1(X0)
      | v2_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_wellord1(X1)
      | ~ v1_wellord1(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
