%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1706+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:29 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 123 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  236 ( 928 expanded)
%              Number of equality atoms :   14 (  92 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3573,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3447,f3451,f3455,f3459,f3463,f3471,f3475,f3565,f3572])).

fof(f3572,plain,
    ( ~ spl12_4
    | ~ spl12_8
    | spl12_20 ),
    inference(avatar_contradiction_clause,[],[f3570])).

fof(f3570,plain,
    ( $false
    | ~ spl12_4
    | ~ spl12_8
    | spl12_20 ),
    inference(unit_resulting_resolution,[],[f3474,f3458,f3564,f3433])).

fof(f3433,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3368])).

fof(f3368,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f3564,plain,
    ( ~ l1_pre_topc(sK2)
    | spl12_20 ),
    inference(avatar_component_clause,[],[f3563])).

fof(f3563,plain,
    ( spl12_20
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f3458,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f3457])).

fof(f3457,plain,
    ( spl12_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f3474,plain,
    ( l1_pre_topc(sK0)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f3473])).

fof(f3473,plain,
    ( spl12_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f3565,plain,
    ( ~ spl12_20
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | spl12_5
    | spl12_7 ),
    inference(avatar_split_clause,[],[f3561,f3469,f3461,f3453,f3449,f3445,f3563])).

fof(f3445,plain,
    ( spl12_1
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f3449,plain,
    ( spl12_2
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f3453,plain,
    ( spl12_3
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f3461,plain,
    ( spl12_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f3469,plain,
    ( spl12_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f3561,plain,
    ( ~ l1_pre_topc(sK2)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | spl12_5
    | spl12_7 ),
    inference(subsumption_resolution,[],[f3560,f3462])).

fof(f3462,plain,
    ( ~ v2_struct_0(sK2)
    | spl12_5 ),
    inference(avatar_component_clause,[],[f3461])).

fof(f3560,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | spl12_7 ),
    inference(subsumption_resolution,[],[f3557,f3454])).

fof(f3454,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f3453])).

fof(f3557,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl12_1
    | ~ spl12_2
    | spl12_7 ),
    inference(resolution,[],[f3541,f3446])).

fof(f3446,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f3445])).

fof(f3541,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,u1_struct_0(X0))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl12_2
    | spl12_7 ),
    inference(resolution,[],[f3521,f3450])).

fof(f3450,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f3449])).

fof(f3521,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_pre_topc(sK1,X3)
        | m1_subset_1(X2,u1_struct_0(X3))
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X3) )
    | spl12_7 ),
    inference(resolution,[],[f3417,f3470])).

fof(f3470,plain,
    ( ~ v2_struct_0(sK1)
    | spl12_7 ),
    inference(avatar_component_clause,[],[f3469])).

fof(f3417,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3355])).

fof(f3355,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3354])).

fof(f3354,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1846])).

fof(f1846,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f3475,plain,(
    spl12_8 ),
    inference(avatar_split_clause,[],[f3399,f3473])).

fof(f3399,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3374])).

fof(f3374,plain,
    ( ! [X4] :
        ( sK3 != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3347,f3373,f3372,f3371,f3370])).

fof(f3370,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_pre_topc(X1,X2)
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
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

% (20772)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
fof(f3371,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & m1_pre_topc(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3372,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(X2)) )
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_pre_topc(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3373,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( X3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ! [X4] :
          ( sK3 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f3347,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3346])).

fof(f3346,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3337])).

fof(f3337,negated_conjecture,(
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
               => ( m1_pre_topc(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3336])).

fof(f3336,conjecture,(
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
             => ( m1_pre_topc(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ? [X4] :
                        ( X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tmap_1)).

fof(f3471,plain,(
    ~ spl12_7 ),
    inference(avatar_split_clause,[],[f3400,f3469])).

fof(f3400,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3374])).

fof(f3463,plain,(
    ~ spl12_5 ),
    inference(avatar_split_clause,[],[f3402,f3461])).

fof(f3402,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3374])).

fof(f3459,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f3403,f3457])).

fof(f3403,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3374])).

fof(f3455,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f3404,f3453])).

fof(f3404,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f3374])).

fof(f3451,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f3405,f3449])).

fof(f3405,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f3374])).

fof(f3447,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f3436,f3445])).

% (20757)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% (20763)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
fof(f3436,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f3406])).

fof(f3406,plain,(
    ! [X4] :
      ( sK3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f3374])).
%------------------------------------------------------------------------------
