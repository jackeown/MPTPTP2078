%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2052+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:06 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 298 expanded)
%              Number of leaves         :   12 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  379 (2200 expanded)
%              Number of equality atoms :   18 (  72 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f54,f55,f82,f94,f101])).

fof(f101,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f99,f48])).

fof(f48,plain,
    ( ~ r1_waybel_0(sK2,sK3,sK4)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl6_2
  <=> r1_waybel_0(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f99,plain,
    ( r1_waybel_0(sK2,sK3,sK4)
    | ~ spl6_1 ),
    inference(resolution,[],[f98,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_waybel_0(X1,X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X1,X0,X2)
      | ~ sP0(X0,X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(superposition,[],[f37,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sK5(X0,X1,X2) = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_waybel_0(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ( r1_waybel_0(X1,X0,sK5(X0,X1,X2))
          & sK5(X0,X1,X2) = X2
          & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_0(X1,X0,X4)
          & X2 = X4
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r1_waybel_0(X1,X0,sK5(X0,X1,X2))
        & sK5(X0,X1,X2) = X2
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_waybel_0(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ? [X4] :
            ( r1_waybel_0(X1,X0,X4)
            & X2 = X4
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ! [X3] :
            ( ~ r1_waybel_0(X1,X2,X3)
            | X0 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( r1_waybel_0(X1,X2,X3)
          & X0 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X1,X0,sK5(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,
    ( sP0(sK3,sK2,sK4)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f97,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_waybel_0(sK2,sK3,sK4)
      | ~ r2_hidden(sK4,k2_yellow19(sK2,sK3)) )
    & ( ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        & r1_waybel_0(sK2,sK3,sK4) )
      | r2_hidden(sK4,k2_yellow19(sK2,sK3)) )
    & l1_waybel_0(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ r1_waybel_0(X0,X1,X2)
                  | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
                & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & r1_waybel_0(X0,X1,X2) )
                  | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
                | ~ r1_waybel_0(sK2,X1,X2)
                | ~ r2_hidden(X2,k2_yellow19(sK2,X1)) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
                  & r1_waybel_0(sK2,X1,X2) )
                | r2_hidden(X2,k2_yellow19(sK2,X1)) ) )
          & l1_waybel_0(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
              | ~ r1_waybel_0(sK2,X1,X2)
              | ~ r2_hidden(X2,k2_yellow19(sK2,X1)) )
            & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
                & r1_waybel_0(sK2,X1,X2) )
              | r2_hidden(X2,k2_yellow19(sK2,X1)) ) )
        & l1_waybel_0(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
            | ~ r1_waybel_0(sK2,sK3,X2)
            | ~ r2_hidden(X2,k2_yellow19(sK2,sK3)) )
          & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
              & r1_waybel_0(sK2,sK3,X2) )
            | r2_hidden(X2,k2_yellow19(sK2,sK3)) ) )
      & l1_waybel_0(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
          | ~ r1_waybel_0(sK2,sK3,X2)
          | ~ r2_hidden(X2,k2_yellow19(sK2,sK3)) )
        & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
            & r1_waybel_0(sK2,sK3,X2) )
          | r2_hidden(X2,k2_yellow19(sK2,sK3)) ) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_waybel_0(sK2,sK3,sK4)
        | ~ r2_hidden(sK4,k2_yellow19(sK2,sK3)) )
      & ( ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
          & r1_waybel_0(sK2,sK3,sK4) )
        | r2_hidden(sK4,k2_yellow19(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2)
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2)
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <~> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <~> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (17523)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r2_hidden(X2,k2_yellow19(X0,X1))
              <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow19)).

fof(f97,plain,
    ( sP0(sK3,sK2,sK4)
    | v2_struct_0(sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f96,f26])).

fof(f26,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,
    ( sP0(sK3,sK2,sK4)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f95,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f95,plain,
    ( sP0(sK3,sK2,sK4)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f87,f28])).

fof(f28,plain,(
    l1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,
    ( sP0(sK3,sK2,sK4)
    | ~ l1_waybel_0(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f70,f43])).

fof(f43,plain,
    ( r2_hidden(sK4,k2_yellow19(sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_1
  <=> r2_hidden(sK4,k2_yellow19(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f70,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k2_yellow19(X3,X4))
      | sP0(X4,X3,X5)
      | ~ l1_waybel_0(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f10,f12,f11])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_0(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_yellow19)).

fof(f68,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k2_yellow19(X3,X4))
      | sP0(X4,X3,X5)
      | ~ sP1(X5,X3,X4)
      | ~ l1_waybel_0(X4,X3)
      | v2_struct_0(X4)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => k2_yellow19(X0,X1) = a_2_1_yellow19(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_yellow19)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_yellow19(X1,X2)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f94,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f92,f25])).

fof(f92,plain,
    ( v2_struct_0(sK2)
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f91,f26])).

fof(f91,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f90,f27])).

fof(f90,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f89,f28])).

fof(f89,plain,
    ( ~ l1_waybel_0(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f87,f84])).

fof(f84,plain,
    ( ! [X0] : ~ sP0(X0,sK2,sK4)
    | spl6_3 ),
    inference(resolution,[],[f52,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(superposition,[],[f35,f36])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl6_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f82,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f79,f47])).

fof(f47,plain,
    ( r1_waybel_0(sK2,sK3,sK4)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f79,plain,
    ( ~ r1_waybel_0(sK2,sK3,sK4)
    | spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f78,f62])).

fof(f62,plain,
    ( ! [X0] :
        ( sP0(X0,sK2,sK4)
        | ~ r1_waybel_0(sK2,X0,sK4) )
    | ~ spl6_3 ),
    inference(resolution,[],[f40,f51])).

fof(f51,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_waybel_0(X1,X0,X3)
      | sP0(X0,X1,X3) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_waybel_0(X1,X0,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,
    ( ~ sP0(sK3,sK2,sK4)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f77,f25])).

fof(f77,plain,
    ( ~ sP0(sK3,sK2,sK4)
    | v2_struct_0(sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f76,f26])).

fof(f76,plain,
    ( ~ sP0(sK3,sK2,sK4)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f75,f27])).

fof(f75,plain,
    ( ~ sP0(sK3,sK2,sK4)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f74,f28])).

fof(f74,plain,
    ( ~ sP0(sK3,sK2,sK4)
    | ~ l1_waybel_0(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | spl6_1 ),
    inference(resolution,[],[f69,f44])).

fof(f44,plain,
    ( ~ r2_hidden(sK4,k2_yellow19(sK2,sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ sP0(X1,X0,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f67,f39])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ sP0(X1,X0,X2)
      | ~ sP1(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f34,f32])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_yellow19(X1,X2))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f29,f46,f42])).

fof(f29,plain,
    ( r1_waybel_0(sK2,sK3,sK4)
    | r2_hidden(sK4,k2_yellow19(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f30,f50,f42])).

fof(f30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK4,k2_yellow19(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f31,f50,f46,f42])).

fof(f31,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_waybel_0(sK2,sK3,sK4)
    | ~ r2_hidden(sK4,k2_yellow19(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
