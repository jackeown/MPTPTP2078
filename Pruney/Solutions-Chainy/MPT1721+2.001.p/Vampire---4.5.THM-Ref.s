%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:05 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 574 expanded)
%              Number of leaves         :   14 ( 230 expanded)
%              Depth                    :   20
%              Number of atoms          :  598 (6476 expanded)
%              Number of equality atoms :   38 (  55 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f502,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f439,f448,f501])).

fof(f501,plain,(
    ~ spl5_29 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f499,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4)
    & ~ r1_tsep_1(sK2,sK3)
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK2,sK4)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f10,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(sK1,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k2_tsep_1(sK1,X1,X2),X3)
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,X2),X3)
              & ~ r1_tsep_1(sK2,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(sK2,X3)
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,X2),X3)
            & ~ r1_tsep_1(sK2,X2)
            & m1_pre_topc(X2,X3)
            & m1_pre_topc(sK2,X3)
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X3)
          & ~ r1_tsep_1(sK2,sK3)
          & m1_pre_topc(sK3,X3)
          & m1_pre_topc(sK2,X3)
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X3)
        & ~ r1_tsep_1(sK2,sK3)
        & m1_pre_topc(sK3,X3)
        & m1_pre_topc(sK2,X3)
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4)
      & ~ r1_tsep_1(sK2,sK3)
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK2,sK4)
      & m1_pre_topc(sK4,sK1)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).

fof(f499,plain,
    ( v2_struct_0(sK1)
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f498,f35])).

fof(f35,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f498,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f497,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f497,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f496,f37])).

fof(f37,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f496,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f495,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f495,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f494,f39])).

fof(f39,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f494,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_29 ),
    inference(resolution,[],[f493,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f493,plain,
    ( ~ sP0(sK1,sK3,sK2)
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f492,f34])).

fof(f34,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f492,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ sP0(sK1,sK3,sK2)
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f491,f35])).

fof(f491,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ sP0(sK1,sK3,sK2)
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f489,f41])).

fof(f41,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f489,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ sP0(sK1,sK3,sK2)
    | ~ spl5_29 ),
    inference(resolution,[],[f476,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k2_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k2_tsep_1(X0,X2,X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f476,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X0)
        | ~ m1_pre_topc(sK4,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f472,f45])).

fof(f45,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f472,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4)
        | ~ m1_pre_topc(sK4,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_29 ),
    inference(resolution,[],[f438,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f438,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl5_29
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f448,plain,(
    spl5_28 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | spl5_28 ),
    inference(subsumption_resolution,[],[f446,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f446,plain,
    ( v2_struct_0(sK4)
    | spl5_28 ),
    inference(subsumption_resolution,[],[f445,f69])).

fof(f69,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f64,f35])).

fof(f64,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f46,f41])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f445,plain,
    ( ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl5_28 ),
    inference(subsumption_resolution,[],[f444,f36])).

fof(f444,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl5_28 ),
    inference(subsumption_resolution,[],[f443,f42])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f443,plain,
    ( ~ m1_pre_topc(sK2,sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl5_28 ),
    inference(subsumption_resolution,[],[f442,f38])).

fof(f442,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl5_28 ),
    inference(subsumption_resolution,[],[f441,f43])).

fof(f43,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f441,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl5_28 ),
    inference(resolution,[],[f440,f58])).

fof(f440,plain,
    ( ~ sP0(sK4,sK3,sK2)
    | spl5_28 ),
    inference(resolution,[],[f434,f57])).

fof(f434,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4)
    | spl5_28 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl5_28
  <=> m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f439,plain,
    ( ~ spl5_28
    | spl5_29 ),
    inference(avatar_split_clause,[],[f402,f436,f432])).

fof(f402,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4))
    | ~ m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4) ),
    inference(superposition,[],[f137,f386])).

fof(f386,plain,(
    u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3)) ),
    inference(forward_demodulation,[],[f385,f314])).

fof(f314,plain,(
    k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f313,f36])).

fof(f313,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f309,f44])).

fof(f44,plain,(
    ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f309,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f258,f37])).

fof(f258,plain,(
    ! [X9] :
      ( ~ m1_pre_topc(X9,sK1)
      | k3_xboole_0(u1_struct_0(X9),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,X9,sK3))
      | r1_tsep_1(X9,sK3)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f257,f33])).

fof(f257,plain,(
    ! [X9] :
      ( r1_tsep_1(X9,sK3)
      | k3_xboole_0(u1_struct_0(X9),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,X9,sK3))
      | ~ m1_pre_topc(X9,sK1)
      | v2_struct_0(X9)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f256,f35])).

fof(f256,plain,(
    ! [X9] :
      ( r1_tsep_1(X9,sK3)
      | k3_xboole_0(u1_struct_0(X9),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,X9,sK3))
      | ~ m1_pre_topc(X9,sK1)
      | v2_struct_0(X9)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f239,f38])).

fof(f239,plain,(
    ! [X9] :
      ( r1_tsep_1(X9,sK3)
      | k3_xboole_0(u1_struct_0(X9),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,X9,sK3))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X9,sK1)
      | v2_struct_0(X9)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f235,f39])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | r1_tsep_1(X0,X1)
      | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(X2,X0,X1))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f234,f58])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(X2,X0,X1))
      | r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ sP0(X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f233,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(X2,X0,X1))
      | v2_struct_0(k2_tsep_1(X2,X0,X1))
      | r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ sP0(X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f232,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(X2,X0,X1))
      | ~ v1_pre_topc(k2_tsep_1(X2,X0,X1))
      | v2_struct_0(k2_tsep_1(X2,X0,X1))
      | r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ sP0(X2,X1,X0) ) ),
    inference(resolution,[],[f59,f57])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f385,plain,(
    k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f384,f36])).

fof(f384,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f380,f44])).

fof(f380,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3))
    | r1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f271,f42])).

fof(f271,plain,(
    ! [X14] :
      ( ~ m1_pre_topc(X14,sK4)
      | k3_xboole_0(u1_struct_0(X14),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,X14,sK3))
      | r1_tsep_1(X14,sK3)
      | v2_struct_0(X14) ) ),
    inference(subsumption_resolution,[],[f270,f40])).

fof(f270,plain,(
    ! [X14] :
      ( r1_tsep_1(X14,sK3)
      | k3_xboole_0(u1_struct_0(X14),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,X14,sK3))
      | ~ m1_pre_topc(X14,sK4)
      | v2_struct_0(X14)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f269,f69])).

fof(f269,plain,(
    ! [X14] :
      ( r1_tsep_1(X14,sK3)
      | k3_xboole_0(u1_struct_0(X14),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,X14,sK3))
      | ~ m1_pre_topc(X14,sK4)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f244,f38])).

fof(f244,plain,(
    ! [X14] :
      ( r1_tsep_1(X14,sK3)
      | k3_xboole_0(u1_struct_0(X14),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,X14,sK3))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X14,sK4)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(resolution,[],[f235,f43])).

fof(f137,plain,(
    ! [X15] :
      ( r1_tarski(u1_struct_0(X15),u1_struct_0(sK4))
      | ~ m1_pre_topc(X15,sK4) ) ),
    inference(subsumption_resolution,[],[f136,f80])).

fof(f80,plain,(
    v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f79,f34])).

fof(f79,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f72,f35])).

fof(f72,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f49,f41])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f136,plain,(
    ! [X15] :
      ( ~ m1_pre_topc(X15,sK4)
      | r1_tarski(u1_struct_0(X15),u1_struct_0(sK4))
      | ~ v2_pre_topc(sK4) ) ),
    inference(subsumption_resolution,[],[f120,f69])).

fof(f120,plain,(
    ! [X15] :
      ( ~ m1_pre_topc(X15,sK4)
      | r1_tarski(u1_struct_0(X15),u1_struct_0(sK4))
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X15] :
      ( ~ m1_pre_topc(X15,sK4)
      | r1_tarski(u1_struct_0(X15),u1_struct_0(sK4))
      | ~ m1_pre_topc(X15,sK4)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4) ) ),
    inference(resolution,[],[f51,f97])).

fof(f97,plain,(
    m1_pre_topc(sK4,sK4) ),
    inference(subsumption_resolution,[],[f96,f34])).

fof(f96,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f88,f35])).

fof(f88,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f85,f41])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f50,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (23707)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (23690)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (23698)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (23687)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (23691)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (23688)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (23701)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (23709)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (23687)Refutation not found, incomplete strategy% (23687)------------------------------
% 0.21/0.52  % (23687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23687)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23687)Memory used [KB]: 10618
% 0.21/0.52  % (23687)Time elapsed: 0.098 s
% 0.21/0.52  % (23687)------------------------------
% 0.21/0.52  % (23687)------------------------------
% 1.30/0.52  % (23696)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.30/0.53  % (23699)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.30/0.53  % (23700)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.30/0.53  % (23697)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.30/0.53  % (23700)Refutation not found, incomplete strategy% (23700)------------------------------
% 1.30/0.53  % (23700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (23700)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (23700)Memory used [KB]: 6140
% 1.30/0.53  % (23700)Time elapsed: 0.118 s
% 1.30/0.53  % (23700)------------------------------
% 1.30/0.53  % (23700)------------------------------
% 1.30/0.53  % (23692)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.30/0.53  % (23695)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.30/0.53  % (23693)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.30/0.53  % (23703)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.30/0.54  % (23711)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.30/0.54  % (23704)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.30/0.54  % (23689)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.30/0.54  % (23705)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.30/0.54  % (23712)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.45/0.54  % (23702)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.45/0.54  % (23708)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.45/0.55  % (23706)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.45/0.55  % (23710)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.45/0.56  % (23694)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.45/0.57  % (23712)Refutation found. Thanks to Tanya!
% 1.45/0.57  % SZS status Theorem for theBenchmark
% 1.45/0.57  % SZS output start Proof for theBenchmark
% 1.45/0.57  fof(f502,plain,(
% 1.45/0.57    $false),
% 1.45/0.57    inference(avatar_sat_refutation,[],[f439,f448,f501])).
% 1.45/0.57  fof(f501,plain,(
% 1.45/0.57    ~spl5_29),
% 1.45/0.57    inference(avatar_contradiction_clause,[],[f500])).
% 1.45/0.57  fof(f500,plain,(
% 1.45/0.57    $false | ~spl5_29),
% 1.45/0.57    inference(subsumption_resolution,[],[f499,f33])).
% 1.45/0.57  fof(f33,plain,(
% 1.45/0.57    ~v2_struct_0(sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f26,plain,(
% 1.45/0.57    (((~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK2,sK4) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.45/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f10,f25,f24,f23,f22])).
% 1.45/0.57  fof(f22,plain,(
% 1.45/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  fof(f23,plain,(
% 1.45/0.57    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,sK2,X2),X3) & ~r1_tsep_1(sK2,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK2,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  fof(f24,plain,(
% 1.45/0.57    ? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,sK2,X2),X3) & ~r1_tsep_1(sK2,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK2,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X3) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,X3) & m1_pre_topc(sK2,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  fof(f25,plain,(
% 1.45/0.57    ? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X3) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,X3) & m1_pre_topc(sK2,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK2,sK4) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4))),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  fof(f10,plain,(
% 1.45/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.45/0.57    inference(flattening,[],[f9])).
% 1.45/0.57  fof(f9,plain,(
% 1.45/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f8])).
% 1.45/0.57  fof(f8,negated_conjecture,(
% 1.45/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 1.45/0.57    inference(negated_conjecture,[],[f7])).
% 1.45/0.57  fof(f7,conjecture,(
% 1.45/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).
% 1.45/0.57  fof(f499,plain,(
% 1.45/0.57    v2_struct_0(sK1) | ~spl5_29),
% 1.45/0.57    inference(subsumption_resolution,[],[f498,f35])).
% 1.45/0.57  fof(f35,plain,(
% 1.45/0.57    l1_pre_topc(sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f498,plain,(
% 1.45/0.57    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl5_29),
% 1.45/0.57    inference(subsumption_resolution,[],[f497,f36])).
% 1.45/0.57  fof(f36,plain,(
% 1.45/0.57    ~v2_struct_0(sK2)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f497,plain,(
% 1.45/0.57    v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl5_29),
% 1.45/0.57    inference(subsumption_resolution,[],[f496,f37])).
% 1.45/0.57  fof(f37,plain,(
% 1.45/0.57    m1_pre_topc(sK2,sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f496,plain,(
% 1.45/0.57    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl5_29),
% 1.45/0.57    inference(subsumption_resolution,[],[f495,f38])).
% 1.45/0.57  fof(f38,plain,(
% 1.45/0.57    ~v2_struct_0(sK3)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f495,plain,(
% 1.45/0.57    v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl5_29),
% 1.45/0.57    inference(subsumption_resolution,[],[f494,f39])).
% 1.45/0.57  fof(f39,plain,(
% 1.45/0.57    m1_pre_topc(sK3,sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f494,plain,(
% 1.45/0.57    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl5_29),
% 1.45/0.57    inference(resolution,[],[f493,f58])).
% 1.45/0.57  fof(f58,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f21])).
% 1.45/0.57  fof(f21,plain,(
% 1.45/0.57    ! [X0,X1,X2] : (sP0(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.57    inference(definition_folding,[],[f19,f20])).
% 1.45/0.57  fof(f20,plain,(
% 1.45/0.57    ! [X0,X2,X1] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~sP0(X0,X2,X1))),
% 1.45/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.45/0.57  fof(f19,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.57    inference(flattening,[],[f18])).
% 1.45/0.57  fof(f18,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f5])).
% 1.45/0.57  fof(f5,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 1.45/0.57  fof(f493,plain,(
% 1.45/0.57    ~sP0(sK1,sK3,sK2) | ~spl5_29),
% 1.45/0.57    inference(subsumption_resolution,[],[f492,f34])).
% 1.45/0.57  fof(f34,plain,(
% 1.45/0.57    v2_pre_topc(sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f492,plain,(
% 1.45/0.57    ~v2_pre_topc(sK1) | ~sP0(sK1,sK3,sK2) | ~spl5_29),
% 1.45/0.57    inference(subsumption_resolution,[],[f491,f35])).
% 1.45/0.57  fof(f491,plain,(
% 1.45/0.57    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~sP0(sK1,sK3,sK2) | ~spl5_29),
% 1.45/0.57    inference(subsumption_resolution,[],[f489,f41])).
% 1.45/0.57  fof(f41,plain,(
% 1.45/0.57    m1_pre_topc(sK4,sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f489,plain,(
% 1.45/0.57    ~m1_pre_topc(sK4,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~sP0(sK1,sK3,sK2) | ~spl5_29),
% 1.45/0.57    inference(resolution,[],[f476,f57])).
% 1.45/0.57  fof(f57,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X2,X1),X0) | ~sP0(X0,X1,X2)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f32])).
% 1.45/0.57  fof(f32,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k2_tsep_1(X0,X2,X1)) & ~v2_struct_0(k2_tsep_1(X0,X2,X1))) | ~sP0(X0,X1,X2))),
% 1.45/0.57    inference(rectify,[],[f31])).
% 1.45/0.57  fof(f31,plain,(
% 1.45/0.57    ! [X0,X2,X1] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~sP0(X0,X2,X1))),
% 1.45/0.57    inference(nnf_transformation,[],[f20])).
% 1.45/0.57  fof(f476,plain,(
% 1.45/0.57    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X0) | ~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl5_29),
% 1.45/0.57    inference(subsumption_resolution,[],[f472,f45])).
% 1.45/0.57  fof(f45,plain,(
% 1.45/0.57    ~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f472,plain,(
% 1.45/0.57    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4) | ~m1_pre_topc(sK4,X0) | ~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl5_29),
% 1.45/0.57    inference(resolution,[],[f438,f50])).
% 1.45/0.57  fof(f50,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f28])).
% 1.45/0.57  fof(f28,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.45/0.57    inference(nnf_transformation,[],[f17])).
% 1.45/0.57  fof(f17,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.45/0.57    inference(flattening,[],[f16])).
% 1.45/0.57  fof(f16,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f6])).
% 1.45/0.57  fof(f6,axiom,(
% 1.45/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.45/0.57  fof(f438,plain,(
% 1.45/0.57    r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4)) | ~spl5_29),
% 1.45/0.57    inference(avatar_component_clause,[],[f436])).
% 1.45/0.57  fof(f436,plain,(
% 1.45/0.57    spl5_29 <=> r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.45/0.57  fof(f448,plain,(
% 1.45/0.57    spl5_28),
% 1.45/0.57    inference(avatar_contradiction_clause,[],[f447])).
% 1.45/0.57  fof(f447,plain,(
% 1.45/0.57    $false | spl5_28),
% 1.45/0.57    inference(subsumption_resolution,[],[f446,f40])).
% 1.45/0.57  fof(f40,plain,(
% 1.45/0.57    ~v2_struct_0(sK4)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f446,plain,(
% 1.45/0.57    v2_struct_0(sK4) | spl5_28),
% 1.45/0.57    inference(subsumption_resolution,[],[f445,f69])).
% 1.45/0.57  fof(f69,plain,(
% 1.45/0.57    l1_pre_topc(sK4)),
% 1.45/0.57    inference(subsumption_resolution,[],[f64,f35])).
% 1.45/0.57  fof(f64,plain,(
% 1.45/0.57    l1_pre_topc(sK4) | ~l1_pre_topc(sK1)),
% 1.45/0.57    inference(resolution,[],[f46,f41])).
% 1.45/0.57  fof(f46,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f11])).
% 1.45/0.57  fof(f11,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f3])).
% 1.45/0.57  fof(f3,axiom,(
% 1.45/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.45/0.57  fof(f445,plain,(
% 1.45/0.57    ~l1_pre_topc(sK4) | v2_struct_0(sK4) | spl5_28),
% 1.45/0.57    inference(subsumption_resolution,[],[f444,f36])).
% 1.45/0.57  fof(f444,plain,(
% 1.45/0.57    v2_struct_0(sK2) | ~l1_pre_topc(sK4) | v2_struct_0(sK4) | spl5_28),
% 1.45/0.57    inference(subsumption_resolution,[],[f443,f42])).
% 1.45/0.57  fof(f42,plain,(
% 1.45/0.57    m1_pre_topc(sK2,sK4)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f443,plain,(
% 1.45/0.57    ~m1_pre_topc(sK2,sK4) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | v2_struct_0(sK4) | spl5_28),
% 1.45/0.57    inference(subsumption_resolution,[],[f442,f38])).
% 1.45/0.57  fof(f442,plain,(
% 1.45/0.57    v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK4) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | v2_struct_0(sK4) | spl5_28),
% 1.45/0.57    inference(subsumption_resolution,[],[f441,f43])).
% 1.45/0.57  fof(f43,plain,(
% 1.45/0.57    m1_pre_topc(sK3,sK4)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f441,plain,(
% 1.45/0.57    ~m1_pre_topc(sK3,sK4) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK4) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | v2_struct_0(sK4) | spl5_28),
% 1.45/0.57    inference(resolution,[],[f440,f58])).
% 1.45/0.57  fof(f440,plain,(
% 1.45/0.57    ~sP0(sK4,sK3,sK2) | spl5_28),
% 1.45/0.57    inference(resolution,[],[f434,f57])).
% 1.45/0.57  fof(f434,plain,(
% 1.45/0.57    ~m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4) | spl5_28),
% 1.45/0.57    inference(avatar_component_clause,[],[f432])).
% 1.45/0.57  fof(f432,plain,(
% 1.45/0.57    spl5_28 <=> m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.45/0.57  fof(f439,plain,(
% 1.45/0.57    ~spl5_28 | spl5_29),
% 1.45/0.57    inference(avatar_split_clause,[],[f402,f436,f432])).
% 1.45/0.57  fof(f402,plain,(
% 1.45/0.57    r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4)) | ~m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4)),
% 1.45/0.57    inference(superposition,[],[f137,f386])).
% 1.45/0.57  fof(f386,plain,(
% 1.45/0.57    u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3))),
% 1.45/0.57    inference(forward_demodulation,[],[f385,f314])).
% 1.45/0.57  fof(f314,plain,(
% 1.45/0.57    k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f313,f36])).
% 1.45/0.57  fof(f313,plain,(
% 1.45/0.57    k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | v2_struct_0(sK2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f309,f44])).
% 1.45/0.57  fof(f44,plain,(
% 1.45/0.57    ~r1_tsep_1(sK2,sK3)),
% 1.45/0.57    inference(cnf_transformation,[],[f26])).
% 1.45/0.57  fof(f309,plain,(
% 1.45/0.57    k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK2)),
% 1.45/0.57    inference(resolution,[],[f258,f37])).
% 1.45/0.57  fof(f258,plain,(
% 1.45/0.57    ( ! [X9] : (~m1_pre_topc(X9,sK1) | k3_xboole_0(u1_struct_0(X9),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,X9,sK3)) | r1_tsep_1(X9,sK3) | v2_struct_0(X9)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f257,f33])).
% 1.45/0.57  fof(f257,plain,(
% 1.45/0.57    ( ! [X9] : (r1_tsep_1(X9,sK3) | k3_xboole_0(u1_struct_0(X9),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,X9,sK3)) | ~m1_pre_topc(X9,sK1) | v2_struct_0(X9) | v2_struct_0(sK1)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f256,f35])).
% 1.45/0.57  fof(f256,plain,(
% 1.45/0.57    ( ! [X9] : (r1_tsep_1(X9,sK3) | k3_xboole_0(u1_struct_0(X9),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,X9,sK3)) | ~m1_pre_topc(X9,sK1) | v2_struct_0(X9) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f239,f38])).
% 1.45/0.57  fof(f239,plain,(
% 1.45/0.57    ( ! [X9] : (r1_tsep_1(X9,sK3) | k3_xboole_0(u1_struct_0(X9),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK1,X9,sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(X9,sK1) | v2_struct_0(X9) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.45/0.57    inference(resolution,[],[f235,f39])).
% 1.45/0.57  fof(f235,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X2) | r1_tsep_1(X0,X1) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(X2,X0,X1)) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f234,f58])).
% 1.45/0.57  fof(f234,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(X2,X0,X1)) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP0(X2,X1,X0)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f233,f55])).
% 1.45/0.57  fof(f55,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X2,X1)) | ~sP0(X0,X1,X2)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f32])).
% 1.45/0.57  fof(f233,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(X2,X0,X1)) | v2_struct_0(k2_tsep_1(X2,X0,X1)) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP0(X2,X1,X0)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f232,f56])).
% 1.45/0.57  fof(f56,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X2,X1)) | ~sP0(X0,X1,X2)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f32])).
% 1.45/0.57  fof(f232,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(X2,X0,X1)) | ~v1_pre_topc(k2_tsep_1(X2,X0,X1)) | v2_struct_0(k2_tsep_1(X2,X0,X1)) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP0(X2,X1,X0)) )),
% 1.45/0.57    inference(resolution,[],[f59,f57])).
% 1.45/0.57  fof(f59,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/0.57    inference(equality_resolution,[],[f47])).
% 1.45/0.57  fof(f47,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f27])).
% 1.45/0.57  fof(f27,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.57    inference(nnf_transformation,[],[f13])).
% 1.45/0.57  fof(f13,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.57    inference(flattening,[],[f12])).
% 1.45/0.57  fof(f12,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f4])).
% 1.45/0.57  fof(f4,axiom,(
% 1.45/0.57    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).
% 1.45/0.57  fof(f385,plain,(
% 1.45/0.57    k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f384,f36])).
% 1.45/0.57  fof(f384,plain,(
% 1.45/0.57    k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3)) | v2_struct_0(sK2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f380,f44])).
% 1.45/0.57  fof(f380,plain,(
% 1.45/0.57    k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3)) | r1_tsep_1(sK2,sK3) | v2_struct_0(sK2)),
% 1.45/0.57    inference(resolution,[],[f271,f42])).
% 1.45/0.57  fof(f271,plain,(
% 1.45/0.57    ( ! [X14] : (~m1_pre_topc(X14,sK4) | k3_xboole_0(u1_struct_0(X14),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,X14,sK3)) | r1_tsep_1(X14,sK3) | v2_struct_0(X14)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f270,f40])).
% 1.45/0.57  fof(f270,plain,(
% 1.45/0.57    ( ! [X14] : (r1_tsep_1(X14,sK3) | k3_xboole_0(u1_struct_0(X14),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,X14,sK3)) | ~m1_pre_topc(X14,sK4) | v2_struct_0(X14) | v2_struct_0(sK4)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f269,f69])).
% 1.45/0.57  fof(f269,plain,(
% 1.45/0.57    ( ! [X14] : (r1_tsep_1(X14,sK3) | k3_xboole_0(u1_struct_0(X14),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,X14,sK3)) | ~m1_pre_topc(X14,sK4) | v2_struct_0(X14) | ~l1_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f244,f38])).
% 1.45/0.57  fof(f244,plain,(
% 1.45/0.57    ( ! [X14] : (r1_tsep_1(X14,sK3) | k3_xboole_0(u1_struct_0(X14),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,X14,sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(X14,sK4) | v2_struct_0(X14) | ~l1_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.45/0.57    inference(resolution,[],[f235,f43])).
% 1.45/0.57  fof(f137,plain,(
% 1.45/0.57    ( ! [X15] : (r1_tarski(u1_struct_0(X15),u1_struct_0(sK4)) | ~m1_pre_topc(X15,sK4)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f136,f80])).
% 1.45/0.57  fof(f80,plain,(
% 1.45/0.57    v2_pre_topc(sK4)),
% 1.45/0.57    inference(subsumption_resolution,[],[f79,f34])).
% 1.45/0.57  fof(f79,plain,(
% 1.45/0.57    v2_pre_topc(sK4) | ~v2_pre_topc(sK1)),
% 1.45/0.57    inference(subsumption_resolution,[],[f72,f35])).
% 1.45/0.57  fof(f72,plain,(
% 1.45/0.57    v2_pre_topc(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.45/0.57    inference(resolution,[],[f49,f41])).
% 1.45/0.57  fof(f49,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f15])).
% 1.45/0.57  fof(f15,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.45/0.57    inference(flattening,[],[f14])).
% 1.45/0.57  fof(f14,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f2])).
% 1.45/0.57  fof(f2,axiom,(
% 1.45/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.45/0.57  fof(f136,plain,(
% 1.45/0.57    ( ! [X15] : (~m1_pre_topc(X15,sK4) | r1_tarski(u1_struct_0(X15),u1_struct_0(sK4)) | ~v2_pre_topc(sK4)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f120,f69])).
% 1.45/0.57  fof(f120,plain,(
% 1.45/0.57    ( ! [X15] : (~m1_pre_topc(X15,sK4) | r1_tarski(u1_struct_0(X15),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)) )),
% 1.45/0.57    inference(duplicate_literal_removal,[],[f119])).
% 1.45/0.57  fof(f119,plain,(
% 1.45/0.57    ( ! [X15] : (~m1_pre_topc(X15,sK4) | r1_tarski(u1_struct_0(X15),u1_struct_0(sK4)) | ~m1_pre_topc(X15,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)) )),
% 1.45/0.57    inference(resolution,[],[f51,f97])).
% 1.45/0.57  fof(f97,plain,(
% 1.45/0.57    m1_pre_topc(sK4,sK4)),
% 1.45/0.57    inference(subsumption_resolution,[],[f96,f34])).
% 1.45/0.57  fof(f96,plain,(
% 1.45/0.57    m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK1)),
% 1.45/0.57    inference(subsumption_resolution,[],[f88,f35])).
% 1.45/0.57  fof(f88,plain,(
% 1.45/0.57    m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.45/0.57    inference(resolution,[],[f85,f41])).
% 1.45/0.57  fof(f85,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 1.45/0.57    inference(duplicate_literal_removal,[],[f84])).
% 1.45/0.57  fof(f84,plain,(
% 1.45/0.57    ( ! [X0,X1] : (m1_pre_topc(X0,X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 1.45/0.57    inference(resolution,[],[f50,f60])).
% 1.45/0.57  fof(f60,plain,(
% 1.45/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.45/0.57    inference(equality_resolution,[],[f53])).
% 1.45/0.57  fof(f53,plain,(
% 1.45/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.45/0.57    inference(cnf_transformation,[],[f30])).
% 1.45/0.57  fof(f30,plain,(
% 1.45/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.57    inference(flattening,[],[f29])).
% 1.45/0.57  fof(f29,plain,(
% 1.45/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.57    inference(nnf_transformation,[],[f1])).
% 1.45/0.57  fof(f1,axiom,(
% 1.45/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.45/0.57  fof(f51,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f28])).
% 1.45/0.57  % SZS output end Proof for theBenchmark
% 1.45/0.57  % (23712)------------------------------
% 1.45/0.57  % (23712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (23712)Termination reason: Refutation
% 1.45/0.57  
% 1.45/0.57  % (23712)Memory used [KB]: 11001
% 1.45/0.57  % (23712)Time elapsed: 0.120 s
% 1.45/0.57  % (23712)------------------------------
% 1.45/0.57  % (23712)------------------------------
% 1.45/0.57  % (23686)Success in time 0.207 s
%------------------------------------------------------------------------------
