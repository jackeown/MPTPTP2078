%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 457 expanded)
%              Number of leaves         :   23 ( 176 expanded)
%              Depth                    :   19
%              Number of atoms          :  729 (4756 expanded)
%              Number of equality atoms :   53 ( 837 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f576,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f244,f253,f255,f406,f409,f528,f575])).

fof(f575,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f573,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ! [X4] :
        ( sK3 != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
    & ! [X5] :
        ( sK3 != X5
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    & ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
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
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2))) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                & ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2))) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              & ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2))) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(X2)) )
            & ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2))) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          & ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( X3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        & ! [X5] :
            ( X3 != X5
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
   => ( ! [X4] :
          ( sK3 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      & ! [X5] :
          ( sK3 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,negated_conjecture,(
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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X1))
                           => X3 != X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ~ ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X2))
                         => X3 != X4 )
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => X3 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).

fof(f573,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f572,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f572,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f571,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f571,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f570,f46])).

fof(f46,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f570,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f569,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f569,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f560,f48])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f560,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f115,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f115,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_4
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f528,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f526,f73])).

fof(f73,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X5] :
      ( sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f526,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl5_7 ),
    inference(resolution,[],[f405,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f405,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl5_7
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f409,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f407,f72])).

fof(f72,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4] :
      ( sK3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f407,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl5_6 ),
    inference(resolution,[],[f402,f56])).

fof(f402,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl5_6
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f406,plain,
    ( spl5_6
    | spl5_7
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f399,f84,f404,f401])).

fof(f84,plain,
    ( spl5_1
  <=> r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f399,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f398,f42])).

fof(f398,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f397,f44])).

fof(f397,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f396,f45])).

fof(f396,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f395,f46])).

fof(f395,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f394,f47])).

fof(f394,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f386,f48])).

% (20014)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f386,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f183,f85])).

fof(f85,plain,
    ( r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f183,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_hidden(X16,u1_struct_0(k1_tsep_1(X15,X13,X14)))
      | r2_hidden(X16,u1_struct_0(X13))
      | r2_hidden(X16,u1_struct_0(X14))
      | ~ m1_pre_topc(X14,X15)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X13,X15)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X15) ) ),
    inference(subsumption_resolution,[],[f182,f62])).

fof(f182,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_hidden(X16,u1_struct_0(k1_tsep_1(X15,X13,X14)))
      | r2_hidden(X16,u1_struct_0(X13))
      | r2_hidden(X16,u1_struct_0(X14))
      | v2_struct_0(k1_tsep_1(X15,X13,X14))
      | ~ m1_pre_topc(X14,X15)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X13,X15)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X15) ) ),
    inference(subsumption_resolution,[],[f181,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f181,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_hidden(X16,u1_struct_0(k1_tsep_1(X15,X13,X14)))
      | r2_hidden(X16,u1_struct_0(X13))
      | r2_hidden(X16,u1_struct_0(X14))
      | ~ v1_pre_topc(k1_tsep_1(X15,X13,X14))
      | v2_struct_0(k1_tsep_1(X15,X13,X14))
      | ~ m1_pre_topc(X14,X15)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X13,X15)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X15) ) ),
    inference(subsumption_resolution,[],[f137,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f137,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_hidden(X16,u1_struct_0(k1_tsep_1(X15,X13,X14)))
      | r2_hidden(X16,u1_struct_0(X13))
      | r2_hidden(X16,u1_struct_0(X14))
      | ~ m1_pre_topc(k1_tsep_1(X15,X13,X14),X15)
      | ~ v1_pre_topc(k1_tsep_1(X15,X13,X14))
      | v2_struct_0(k1_tsep_1(X15,X13,X14))
      | ~ m1_pre_topc(X14,X15)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X13,X15)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X15) ) ),
    inference(superposition,[],[f77,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

% (20015)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f255,plain,
    ( ~ spl5_3
    | ~ spl5_2
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f108,f117,f114,f87,f111])).

fof(f111,plain,
    ( spl5_3
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f87,plain,
    ( spl5_2
  <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f117,plain,
    ( spl5_5
  <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f108,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f107,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f95,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_connsp_2(X1,X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f58,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f253,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f251,f42])).

fof(f251,plain,
    ( v2_struct_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f250,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f250,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f249,f44])).

fof(f249,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f248,f45])).

fof(f248,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f247,f46])).

fof(f247,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f246,f47])).

fof(f246,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f245,f48])).

fof(f245,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_5 ),
    inference(resolution,[],[f118,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tmap_1)).

fof(f118,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f244,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f242,f48])).

fof(f242,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f241,f42])).

fof(f241,plain,
    ( v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f240,f44])).

fof(f240,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f239,f45])).

fof(f239,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f238,f46])).

fof(f238,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f237,f47])).

fof(f237,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | spl5_3 ),
    inference(resolution,[],[f105,f112])).

fof(f112,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(k1_tsep_1(X1,X2,X0))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | l1_pre_topc(k1_tsep_1(X1,X2,X0))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f89,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f82,f87,f84])).

fof(f82,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(resolution,[],[f57,f49])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:14:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (20001)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (19999)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (19998)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (19998)Refutation not found, incomplete strategy% (19998)------------------------------
% 0.22/0.49  % (19998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (19998)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (19998)Memory used [KB]: 10618
% 0.22/0.49  % (19998)Time elapsed: 0.070 s
% 0.22/0.49  % (19998)------------------------------
% 0.22/0.49  % (19998)------------------------------
% 0.22/0.49  % (20010)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (19997)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (20008)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (20011)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (20002)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (20000)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (20016)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (20003)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (20012)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (20005)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (19999)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f576,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f89,f244,f253,f255,f406,f409,f528,f575])).
% 0.22/0.51  fof(f575,plain,(
% 0.22/0.51    ~spl5_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f574])).
% 0.22/0.51  fof(f574,plain,(
% 0.22/0.51    $false | ~spl5_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f573,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    (((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f34,f33,f32,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2)))) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2)))) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2)))) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2)))) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) => (! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 0.22/0.51    inference(rectify,[],[f12])).
% 0.22/0.51  fof(f12,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f11])).
% 0.22/0.51  fof(f11,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).
% 0.22/0.51  fof(f573,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~spl5_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f572,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f572,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f571,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f571,plain,(
% 0.22/0.51    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f570,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f570,plain,(
% 0.22/0.51    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f569,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~v2_struct_0(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f569,plain,(
% 0.22/0.51    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f560,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f560,plain,(
% 0.22/0.51    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_4),
% 0.22/0.51    inference(resolution,[],[f115,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~spl5_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f114])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl5_4 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.51  fof(f528,plain,(
% 0.22/0.51    ~spl5_7),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f527])).
% 0.22/0.51  fof(f527,plain,(
% 0.22/0.51    $false | ~spl5_7),
% 0.22/0.51    inference(subsumption_resolution,[],[f526,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.22/0.51    inference(equality_resolution,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f526,plain,(
% 0.22/0.51    m1_subset_1(sK3,u1_struct_0(sK1)) | ~spl5_7),
% 0.22/0.51    inference(resolution,[],[f405,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.51  fof(f405,plain,(
% 0.22/0.51    r2_hidden(sK3,u1_struct_0(sK1)) | ~spl5_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f404])).
% 0.22/0.51  fof(f404,plain,(
% 0.22/0.51    spl5_7 <=> r2_hidden(sK3,u1_struct_0(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.51  fof(f409,plain,(
% 0.22/0.51    ~spl5_6),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f408])).
% 0.22/0.51  fof(f408,plain,(
% 0.22/0.51    $false | ~spl5_6),
% 0.22/0.51    inference(subsumption_resolution,[],[f407,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.22/0.51    inference(equality_resolution,[],[f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f407,plain,(
% 0.22/0.51    m1_subset_1(sK3,u1_struct_0(sK2)) | ~spl5_6),
% 0.22/0.51    inference(resolution,[],[f402,f56])).
% 0.22/0.51  fof(f402,plain,(
% 0.22/0.51    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl5_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f401])).
% 0.22/0.51  fof(f401,plain,(
% 0.22/0.51    spl5_6 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.51  fof(f406,plain,(
% 0.22/0.51    spl5_6 | spl5_7 | ~spl5_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f399,f84,f404,f401])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    spl5_1 <=> r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.51  fof(f399,plain,(
% 0.22/0.51    r2_hidden(sK3,u1_struct_0(sK1)) | r2_hidden(sK3,u1_struct_0(sK2)) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f398,f42])).
% 0.22/0.51  fof(f398,plain,(
% 0.22/0.51    r2_hidden(sK3,u1_struct_0(sK1)) | r2_hidden(sK3,u1_struct_0(sK2)) | v2_struct_0(sK0) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f397,f44])).
% 0.22/0.51  fof(f397,plain,(
% 0.22/0.51    r2_hidden(sK3,u1_struct_0(sK1)) | r2_hidden(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f396,f45])).
% 0.22/0.51  fof(f396,plain,(
% 0.22/0.51    r2_hidden(sK3,u1_struct_0(sK1)) | r2_hidden(sK3,u1_struct_0(sK2)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f395,f46])).
% 0.22/0.51  fof(f395,plain,(
% 0.22/0.51    r2_hidden(sK3,u1_struct_0(sK1)) | r2_hidden(sK3,u1_struct_0(sK2)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f394,f47])).
% 0.22/0.51  fof(f394,plain,(
% 0.22/0.51    r2_hidden(sK3,u1_struct_0(sK1)) | r2_hidden(sK3,u1_struct_0(sK2)) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f386,f48])).
% 0.22/0.51  % (20014)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  fof(f386,plain,(
% 0.22/0.51    r2_hidden(sK3,u1_struct_0(sK1)) | r2_hidden(sK3,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.22/0.51    inference(resolution,[],[f183,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl5_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f84])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ( ! [X14,X15,X13,X16] : (~r2_hidden(X16,u1_struct_0(k1_tsep_1(X15,X13,X14))) | r2_hidden(X16,u1_struct_0(X13)) | r2_hidden(X16,u1_struct_0(X14)) | ~m1_pre_topc(X14,X15) | v2_struct_0(X14) | ~m1_pre_topc(X13,X15) | v2_struct_0(X13) | ~l1_pre_topc(X15) | v2_struct_0(X15)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f182,f62])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ( ! [X14,X15,X13,X16] : (~r2_hidden(X16,u1_struct_0(k1_tsep_1(X15,X13,X14))) | r2_hidden(X16,u1_struct_0(X13)) | r2_hidden(X16,u1_struct_0(X14)) | v2_struct_0(k1_tsep_1(X15,X13,X14)) | ~m1_pre_topc(X14,X15) | v2_struct_0(X14) | ~m1_pre_topc(X13,X15) | v2_struct_0(X13) | ~l1_pre_topc(X15) | v2_struct_0(X15)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f181,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    ( ! [X14,X15,X13,X16] : (~r2_hidden(X16,u1_struct_0(k1_tsep_1(X15,X13,X14))) | r2_hidden(X16,u1_struct_0(X13)) | r2_hidden(X16,u1_struct_0(X14)) | ~v1_pre_topc(k1_tsep_1(X15,X13,X14)) | v2_struct_0(k1_tsep_1(X15,X13,X14)) | ~m1_pre_topc(X14,X15) | v2_struct_0(X14) | ~m1_pre_topc(X13,X15) | v2_struct_0(X13) | ~l1_pre_topc(X15) | v2_struct_0(X15)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f137,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    ( ! [X14,X15,X13,X16] : (~r2_hidden(X16,u1_struct_0(k1_tsep_1(X15,X13,X14))) | r2_hidden(X16,u1_struct_0(X13)) | r2_hidden(X16,u1_struct_0(X14)) | ~m1_pre_topc(k1_tsep_1(X15,X13,X14),X15) | ~v1_pre_topc(k1_tsep_1(X15,X13,X14)) | v2_struct_0(k1_tsep_1(X15,X13,X14)) | ~m1_pre_topc(X14,X15) | v2_struct_0(X14) | ~m1_pre_topc(X13,X15) | v2_struct_0(X13) | ~l1_pre_topc(X15) | v2_struct_0(X15)) )),
% 0.22/0.51    inference(superposition,[],[f77,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.51    inference(rectify,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.51    inference(flattening,[],[f37])).
% 0.22/0.51  % (20015)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    ~spl5_3 | ~spl5_2 | spl5_4 | ~spl5_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f108,f117,f114,f87,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl5_3 <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl5_2 <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl5_5 <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 0.22/0.51    inference(resolution,[],[f107,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f106])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(resolution,[],[f95,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_connsp_2(X1,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v1_xboole_0(u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.22/0.51    inference(resolution,[],[f58,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 0.22/0.51  fof(f253,plain,(
% 0.22/0.51    spl5_5),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f252])).
% 0.22/0.51  fof(f252,plain,(
% 0.22/0.51    $false | spl5_5),
% 0.22/0.51    inference(subsumption_resolution,[],[f251,f42])).
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    v2_struct_0(sK0) | spl5_5),
% 0.22/0.51    inference(subsumption_resolution,[],[f250,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_5),
% 0.22/0.51    inference(subsumption_resolution,[],[f249,f44])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_5),
% 0.22/0.51    inference(subsumption_resolution,[],[f248,f45])).
% 0.22/0.51  fof(f248,plain,(
% 0.22/0.51    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_5),
% 0.22/0.51    inference(subsumption_resolution,[],[f247,f46])).
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_5),
% 0.22/0.51    inference(subsumption_resolution,[],[f246,f47])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_5),
% 0.22/0.51    inference(subsumption_resolution,[],[f245,f48])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_5),
% 0.22/0.51    inference(resolution,[],[f118,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tmap_1)).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl5_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    spl5_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f243])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    $false | spl5_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f242,f48])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    ~m1_pre_topc(sK2,sK0) | spl5_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f241,f42])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~m1_pre_topc(sK2,sK0) | spl5_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f240,f44])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK2,sK0) | spl5_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f239,f45])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK2,sK0) | spl5_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f238,f46])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK2,sK0) | spl5_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f237,f47])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK2,sK0) | spl5_3),
% 0.22/0.51    inference(resolution,[],[f105,f112])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl5_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f111])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (l1_pre_topc(k1_tsep_1(X1,X2,X0)) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | l1_pre_topc(k1_tsep_1(X1,X2,X0)) | ~l1_pre_topc(X1)) )),
% 0.22/0.51    inference(resolution,[],[f64,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl5_1 | spl5_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f82,f87,f84])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.22/0.51    inference(resolution,[],[f57,f49])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (19999)------------------------------
% 0.22/0.51  % (19999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19999)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (19999)Memory used [KB]: 11001
% 0.22/0.51  % (19999)Time elapsed: 0.089 s
% 0.22/0.51  % (19999)------------------------------
% 0.22/0.51  % (19999)------------------------------
% 0.22/0.51  % (19996)Success in time 0.15 s
%------------------------------------------------------------------------------
