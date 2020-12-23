%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1123+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:08 EST 2020

% Result     : Theorem 47.49s
% Output     : Refutation 47.49s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 663 expanded)
%              Number of leaves         :   42 ( 249 expanded)
%              Depth                    :   20
%              Number of atoms          : 1038 (6476 expanded)
%              Number of equality atoms :   56 ( 135 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45599,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2876,f2881,f2886,f2891,f2895,f2896,f3966,f4067,f4904,f4915,f4916,f4917,f6220,f12399,f12629,f13103,f13799,f20665,f21120,f45372])).

fof(f45372,plain,
    ( spl72_7
    | ~ spl72_1
    | ~ spl72_66 ),
    inference(avatar_split_clause,[],[f21235,f4017,f2865,f2893])).

fof(f2893,plain,
    ( spl72_7
  <=> ! [X4] :
        ( ~ r1_xboole_0(sK3,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(X4,sK2)
        | ~ r2_hidden(sK4,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_7])])).

fof(f2865,plain,
    ( spl72_1
  <=> r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_1])])).

fof(f4017,plain,
    ( spl72_66
  <=> m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_66])])).

fof(f21235,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK3,X1)
        | ~ r2_hidden(sK4,X1)
        | ~ v3_pre_topc(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl72_1
    | ~ spl72_66 ),
    inference(subsumption_resolution,[],[f21234,f2466])).

fof(f2466,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1943])).

fof(f1943,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f488])).

fof(f488,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f21234,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK3,X1)
        | ~ r2_hidden(sK4,X1)
        | ~ v3_pre_topc(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(sK4,u1_struct_0(sK2)) )
    | ~ spl72_1
    | ~ spl72_66 ),
    inference(subsumption_resolution,[],[f21233,f2345])).

fof(f2345,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f2167])).

fof(f2167,plain,
    ( ( ( r1_xboole_0(sK3,sK5)
        & r2_hidden(sK4,sK5)
        & v3_pre_topc(sK5,sK2)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) )
      | v2_struct_0(sK2)
      | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) )
    & ( ( ! [X4] :
            ( ~ r1_xboole_0(sK3,X4)
            | ~ r2_hidden(sK4,X4)
            | ~ v3_pre_topc(X4,sK2)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
        & ~ v2_struct_0(sK2) )
      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f2162,f2166,f2165,f2164,f2163])).

fof(f2163,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0)
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,sK2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
                | v2_struct_0(sK2)
                | ~ r2_hidden(X2,k2_pre_topc(sK2,X1)) )
              & ( ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,sK2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
                  & ~ v2_struct_0(sK2) )
                | r2_hidden(X2,k2_pre_topc(sK2,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2164,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( r1_xboole_0(X1,X3)
                  & r2_hidden(X2,X3)
                  & v3_pre_topc(X3,sK2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              | v2_struct_0(sK2)
              | ~ r2_hidden(X2,k2_pre_topc(sK2,X1)) )
            & ( ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,sK2)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
                & ~ v2_struct_0(sK2) )
              | r2_hidden(X2,k2_pre_topc(sK2,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( r1_xboole_0(sK3,X3)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,sK2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            | v2_struct_0(sK2)
            | ~ r2_hidden(X2,k2_pre_topc(sK2,sK3)) )
          & ( ( ! [X4] :
                  ( ~ r1_xboole_0(sK3,X4)
                  | ~ r2_hidden(X2,X4)
                  | ~ v3_pre_topc(X4,sK2)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
              & ~ v2_struct_0(sK2) )
            | r2_hidden(X2,k2_pre_topc(sK2,sK3)) )
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f2165,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( r1_xboole_0(sK3,X3)
              & r2_hidden(X2,X3)
              & v3_pre_topc(X3,sK2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          | v2_struct_0(sK2)
          | ~ r2_hidden(X2,k2_pre_topc(sK2,sK3)) )
        & ( ( ! [X4] :
                ( ~ r1_xboole_0(sK3,X4)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,sK2)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
            & ~ v2_struct_0(sK2) )
          | r2_hidden(X2,k2_pre_topc(sK2,sK3)) )
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( ( ? [X3] :
            ( r1_xboole_0(sK3,X3)
            & r2_hidden(sK4,X3)
            & v3_pre_topc(X3,sK2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        | v2_struct_0(sK2)
        | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) )
      & ( ( ! [X4] :
              ( ~ r1_xboole_0(sK3,X4)
              | ~ r2_hidden(sK4,X4)
              | ~ v3_pre_topc(X4,sK2)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
          & ~ v2_struct_0(sK2) )
        | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f2166,plain,
    ( ? [X3] :
        ( r1_xboole_0(sK3,X3)
        & r2_hidden(sK4,X3)
        & v3_pre_topc(X3,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( r1_xboole_0(sK3,sK5)
      & r2_hidden(sK4,sK5)
      & v3_pre_topc(sK5,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f2162,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v2_struct_0(X0)
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2161])).

fof(f2161,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v2_struct_0(X0)
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2160])).

fof(f2160,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v2_struct_0(X0)
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1849])).

fof(f1849,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1848])).

fof(f1848,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1837])).

fof(f1837,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_xboole_0(X1,X3)
                            & r2_hidden(X2,X3)
                            & v3_pre_topc(X3,X0) ) )
                    & ~ v2_struct_0(X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1836])).

fof(f1836,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).

fof(f21233,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK3,X1)
        | ~ r2_hidden(sK4,X1)
        | ~ v3_pre_topc(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(sK4,u1_struct_0(sK2))
        | ~ l1_pre_topc(sK2) )
    | ~ spl72_1
    | ~ spl72_66 ),
    inference(subsumption_resolution,[],[f21232,f2346])).

fof(f2346,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f2167])).

fof(f21232,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK3,X1)
        | ~ r2_hidden(sK4,X1)
        | ~ v3_pre_topc(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(sK4,u1_struct_0(sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2) )
    | ~ spl72_1
    | ~ spl72_66 ),
    inference(subsumption_resolution,[],[f13225,f4018])).

fof(f4018,plain,
    ( m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl72_66 ),
    inference(avatar_component_clause,[],[f4017])).

fof(f13225,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK3,X1)
        | ~ r2_hidden(sK4,X1)
        | ~ v3_pre_topc(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(sK4,u1_struct_0(sK2))
        | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2) )
    | ~ spl72_1 ),
    inference(resolution,[],[f2866,f2828])).

fof(f2828,plain,(
    ! [X6,X0,X8,X1] :
      ( ~ r1_xboole_0(X1,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2420])).

fof(f2420,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( ~ r1_xboole_0(X1,X8)
      | ~ r2_hidden(X6,X8)
      | ~ v3_pre_topc(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2196])).

fof(f2196,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ( ( ( r1_xboole_0(X1,sK20(X0,X1,X2))
                        & r2_hidden(sK19(X0,X1,X2),sK20(X0,X1,X2))
                        & v3_pre_topc(sK20(X0,X1,X2),X0)
                        & m1_subset_1(sK20(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ r2_hidden(sK19(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( ~ r1_xboole_0(X1,X5)
                          | ~ r2_hidden(sK19(X0,X1,X2),X5)
                          | ~ v3_pre_topc(X5,X0)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                      | r2_hidden(sK19(X0,X1,X2),X2) )
                    & r2_hidden(sK19(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( r1_xboole_0(X1,sK21(X0,X1,X6))
                            & r2_hidden(X6,sK21(X0,X1,X6))
                            & v3_pre_topc(sK21(X0,X1,X6),X0)
                            & m1_subset_1(sK21(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X8] :
                              ( ~ r1_xboole_0(X1,X8)
                              | ~ r2_hidden(X6,X8)
                              | ~ v3_pre_topc(X8,X0)
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ r2_hidden(X6,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20,sK21])],[f2192,f2195,f2194,f2193])).

fof(f2193,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( r1_xboole_0(X1,X4)
                & r2_hidden(X3,X4)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( ~ r1_xboole_0(X1,X5)
                | ~ r2_hidden(X3,X5)
                | ~ v3_pre_topc(X5,X0)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X3,X2) )
          & r2_hidden(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( r1_xboole_0(X1,X4)
              & r2_hidden(sK19(X0,X1,X2),X4)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK19(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( ~ r1_xboole_0(X1,X5)
              | ~ r2_hidden(sK19(X0,X1,X2),X5)
              | ~ v3_pre_topc(X5,X0)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK19(X0,X1,X2),X2) )
        & r2_hidden(sK19(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2194,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(X1,X4)
          & r2_hidden(sK19(X0,X1,X2),X4)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK20(X0,X1,X2))
        & r2_hidden(sK19(X0,X1,X2),sK20(X0,X1,X2))
        & v3_pre_topc(sK20(X0,X1,X2),X0)
        & m1_subset_1(sK20(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2195,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( r1_xboole_0(X1,X7)
          & r2_hidden(X6,X7)
          & v3_pre_topc(X7,X0)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK21(X0,X1,X6))
        & r2_hidden(X6,sK21(X0,X1,X6))
        & v3_pre_topc(sK21(X0,X1,X6),X0)
        & m1_subset_1(sK21(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2192,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( ~ r1_xboole_0(X1,X5)
                            | ~ r2_hidden(X3,X5)
                            | ~ v3_pre_topc(X5,X0)
                            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( r1_xboole_0(X1,X7)
                              & r2_hidden(X6,X7)
                              & v3_pre_topc(X7,X0)
                              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X8] :
                              ( ~ r1_xboole_0(X1,X8)
                              | ~ r2_hidden(X6,X8)
                              | ~ v3_pre_topc(X8,X0)
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ r2_hidden(X6,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2191])).

fof(f2191,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( ~ r1_xboole_0(X1,X4)
                            | ~ r2_hidden(X3,X4)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0)
                              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X4] :
                              ( ~ r1_xboole_0(X1,X4)
                              | ~ r2_hidden(X3,X4)
                              | ~ v3_pre_topc(X4,X0)
                              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ r2_hidden(X3,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2190])).

fof(f2190,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( ~ r1_xboole_0(X1,X4)
                            | ~ r2_hidden(X3,X4)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0)
                              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X4] :
                              ( ~ r1_xboole_0(X1,X4)
                              | ~ r2_hidden(X3,X4)
                              | ~ v3_pre_topc(X4,X0)
                              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ r2_hidden(X3,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1906])).

fof(f1906,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1905])).

fof(f1905,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1768])).

fof(f1768,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( r2_hidden(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pre_topc)).

fof(f2866,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ spl72_1 ),
    inference(avatar_component_clause,[],[f2865])).

fof(f21120,plain,(
    ~ spl72_56 ),
    inference(avatar_contradiction_clause,[],[f21119])).

fof(f21119,plain,
    ( $false
    | ~ spl72_56 ),
    inference(subsumption_resolution,[],[f21029,f2823])).

fof(f2823,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f2417])).

fof(f2417,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1904,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f21029,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl72_56 ),
    inference(superposition,[],[f2822,f3965])).

fof(f3965,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl72_56 ),
    inference(avatar_component_clause,[],[f3963])).

fof(f3963,plain,
    ( spl72_56
  <=> k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_56])])).

fof(f2822,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f2378])).

fof(f2378,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f1876])).

fof(f1876,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f372])).

fof(f372,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f20665,plain,
    ( spl72_56
    | ~ spl72_27
    | ~ spl72_36
    | ~ spl72_55
    | spl72_83
    | ~ spl72_119 ),
    inference(avatar_split_clause,[],[f20664,f4891,f4209,f3959,f3416,f3077,f3963])).

fof(f3077,plain,
    ( spl72_27
  <=> k1_xboole_0 = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_27])])).

fof(f3416,plain,
    ( spl72_36
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_36])])).

fof(f3959,plain,
    ( spl72_55
  <=> m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_55])])).

fof(f4209,plain,
    ( spl72_83
  <=> v1_xboole_0(k2_pre_topc(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_83])])).

fof(f4891,plain,
    ( spl72_119
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_119])])).

fof(f20664,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl72_27
    | ~ spl72_36
    | ~ spl72_55
    | spl72_83
    | ~ spl72_119 ),
    inference(forward_demodulation,[],[f20663,f3418])).

fof(f3418,plain,
    ( k1_xboole_0 = sK3
    | ~ spl72_36 ),
    inference(avatar_component_clause,[],[f3416])).

fof(f20663,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | ~ spl72_27
    | ~ spl72_36
    | ~ spl72_55
    | spl72_83
    | ~ spl72_119 ),
    inference(subsumption_resolution,[],[f20662,f20633])).

fof(f20633,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_tarski(k1_xboole_0))
    | ~ spl72_27
    | ~ spl72_36
    | ~ spl72_55
    | spl72_83
    | ~ spl72_119 ),
    inference(forward_demodulation,[],[f20632,f3418])).

fof(f20632,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_tarski(sK3))
    | ~ spl72_27
    | ~ spl72_55
    | spl72_83
    | ~ spl72_119 ),
    inference(subsumption_resolution,[],[f20428,f15202])).

fof(f15202,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
    | ~ spl72_27
    | spl72_83
    | ~ spl72_119 ),
    inference(forward_demodulation,[],[f15201,f2575])).

fof(f2575,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f15201,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl72_27
    | spl72_83
    | ~ spl72_119 ),
    inference(forward_demodulation,[],[f15200,f3079])).

fof(f3079,plain,
    ( k1_xboole_0 = u1_struct_0(sK2)
    | ~ spl72_27 ),
    inference(avatar_component_clause,[],[f3077])).

fof(f15200,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl72_83
    | ~ spl72_119 ),
    inference(subsumption_resolution,[],[f15199,f13783])).

fof(f13783,plain,
    ( ! [X15] :
        ( v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl72_119 ),
    inference(resolution,[],[f4893,f2662])).

fof(f2662,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2051])).

fof(f2051,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f541])).

fof(f541,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f4893,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl72_119 ),
    inference(avatar_component_clause,[],[f4891])).

fof(f15199,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | spl72_83
    | ~ spl72_119 ),
    inference(subsumption_resolution,[],[f15198,f2345])).

fof(f15198,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2) )
    | spl72_83
    | ~ spl72_119 ),
    inference(subsumption_resolution,[],[f15197,f2638])).

fof(f2638,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f15197,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2) )
    | spl72_83
    | ~ spl72_119 ),
    inference(subsumption_resolution,[],[f15141,f13772])).

fof(f13772,plain,
    ( ! [X2] : ~ r2_hidden(X2,u1_struct_0(sK2))
    | ~ spl72_119 ),
    inference(resolution,[],[f4893,f2645])).

fof(f2645,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2038])).

fof(f2038,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f15141,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | r2_hidden(sK19(sK2,k1_xboole_0,X0),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2) )
    | spl72_83 ),
    inference(superposition,[],[f4210,f2425])).

fof(f2425,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,X1) = X2
      | r2_hidden(sK19(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2196])).

fof(f4210,plain,
    ( ~ v1_xboole_0(k2_pre_topc(sK2,k1_xboole_0))
    | spl72_83 ),
    inference(avatar_component_clause,[],[f4209])).

fof(f20428,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | ~ r2_hidden(X0,k1_tarski(sK3)) )
    | ~ spl72_55 ),
    inference(resolution,[],[f3961,f2459])).

fof(f2459,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1938])).

fof(f1938,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f1937])).

fof(f1937,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f3961,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(k1_tarski(k1_xboole_0)))
    | ~ spl72_55 ),
    inference(avatar_component_clause,[],[f3959])).

fof(f20662,plain,
    ( r2_hidden(sK41(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | k1_xboole_0 = k1_tarski(sK3)
    | ~ spl72_36
    | ~ spl72_55 ),
    inference(forward_demodulation,[],[f20451,f3418])).

fof(f20451,plain,
    ( r2_hidden(sK41(k1_tarski(k1_xboole_0),k1_tarski(sK3)),k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK3)
    | ~ spl72_55 ),
    inference(resolution,[],[f3961,f2633])).

fof(f2633,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK41(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2266])).

fof(f2266,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK41(X0,X1),X1)
        & m1_subset_1(sK41(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK41])],[f2033,f2265])).

fof(f2265,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK41(X0,X1),X1)
        & m1_subset_1(sK41(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2033,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2032])).

fof(f2032,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f497])).

fof(f497,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f13799,plain,
    ( spl72_27
    | ~ spl72_119 ),
    inference(avatar_split_clause,[],[f13785,f4891,f3077])).

fof(f13785,plain,
    ( k1_xboole_0 = u1_struct_0(sK2)
    | ~ spl72_119 ),
    inference(resolution,[],[f4893,f2664])).

fof(f2664,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2053])).

fof(f2053,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f13103,plain,
    ( ~ spl72_6
    | ~ spl72_3
    | ~ spl72_4
    | ~ spl72_5
    | ~ spl72_7 ),
    inference(avatar_split_clause,[],[f13102,f2893,f2883,f2878,f2873,f2888])).

fof(f2888,plain,
    ( spl72_6
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_6])])).

fof(f2873,plain,
    ( spl72_3
  <=> r1_xboole_0(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_3])])).

fof(f2878,plain,
    ( spl72_4
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_4])])).

fof(f2883,plain,
    ( spl72_5
  <=> v3_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_5])])).

fof(f13102,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl72_3
    | ~ spl72_4
    | ~ spl72_5
    | ~ spl72_7 ),
    inference(subsumption_resolution,[],[f12826,f2875])).

fof(f2875,plain,
    ( r1_xboole_0(sK3,sK5)
    | ~ spl72_3 ),
    inference(avatar_component_clause,[],[f2873])).

fof(f12826,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(sK3,sK5)
    | ~ spl72_4
    | ~ spl72_5
    | ~ spl72_7 ),
    inference(subsumption_resolution,[],[f12821,f2880])).

fof(f2880,plain,
    ( r2_hidden(sK4,sK5)
    | ~ spl72_4 ),
    inference(avatar_component_clause,[],[f2878])).

fof(f12821,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(sK3,sK5)
    | ~ r2_hidden(sK4,sK5)
    | ~ spl72_5
    | ~ spl72_7 ),
    inference(resolution,[],[f2885,f2894])).

fof(f2894,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(X4,sK2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_xboole_0(sK3,X4)
        | ~ r2_hidden(sK4,X4) )
    | ~ spl72_7 ),
    inference(avatar_component_clause,[],[f2893])).

fof(f2885,plain,
    ( v3_pre_topc(sK5,sK2)
    | ~ spl72_5 ),
    inference(avatar_component_clause,[],[f2883])).

fof(f12629,plain,
    ( ~ spl72_1
    | ~ spl72_36
    | ~ spl72_83 ),
    inference(avatar_contradiction_clause,[],[f12628])).

fof(f12628,plain,
    ( $false
    | ~ spl72_1
    | ~ spl72_36
    | ~ spl72_83 ),
    inference(subsumption_resolution,[],[f12627,f8096])).

fof(f8096,plain,
    ( ! [X2] : ~ r2_hidden(X2,k2_pre_topc(sK2,k1_xboole_0))
    | ~ spl72_83 ),
    inference(resolution,[],[f4211,f2645])).

fof(f4211,plain,
    ( v1_xboole_0(k2_pre_topc(sK2,k1_xboole_0))
    | ~ spl72_83 ),
    inference(avatar_component_clause,[],[f4209])).

fof(f12627,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,k1_xboole_0))
    | ~ spl72_1
    | ~ spl72_36 ),
    inference(forward_demodulation,[],[f2866,f3418])).

fof(f12399,plain,
    ( spl72_1
    | ~ spl72_7
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(avatar_contradiction_clause,[],[f12398])).

fof(f12398,plain,
    ( $false
    | spl72_1
    | ~ spl72_7
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f12397,f5127])).

fof(f5127,plain,
    ( r2_hidden(sK4,sK21(sK2,sK3,sK4))
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5126,f2345])).

fof(f5126,plain,
    ( r2_hidden(sK4,sK21(sK2,sK3,sK4))
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5125,f2346])).

fof(f5125,plain,
    ( r2_hidden(sK4,sK21(sK2,sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5124,f4018])).

fof(f5124,plain,
    ( r2_hidden(sK4,sK21(sK2,sK3,sK4))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5079,f4897])).

fof(f4897,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | ~ spl72_120 ),
    inference(avatar_component_clause,[],[f4895])).

fof(f4895,plain,
    ( spl72_120
  <=> r2_hidden(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_120])])).

fof(f5079,plain,
    ( r2_hidden(sK4,sK21(sK2,sK3,sK4))
    | ~ r2_hidden(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1 ),
    inference(resolution,[],[f2867,f2825])).

fof(f2825,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k2_pre_topc(X0,X1))
      | r2_hidden(X6,sK21(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2423])).

fof(f2423,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r2_hidden(X6,sK21(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2196])).

fof(f2867,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | spl72_1 ),
    inference(avatar_component_clause,[],[f2865])).

fof(f12397,plain,
    ( ~ r2_hidden(sK4,sK21(sK2,sK3,sK4))
    | spl72_1
    | ~ spl72_7
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f12396,f5123])).

fof(f5123,plain,
    ( r1_xboole_0(sK3,sK21(sK2,sK3,sK4))
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5122,f2345])).

fof(f5122,plain,
    ( r1_xboole_0(sK3,sK21(sK2,sK3,sK4))
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5121,f2346])).

fof(f5121,plain,
    ( r1_xboole_0(sK3,sK21(sK2,sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5120,f4018])).

fof(f5120,plain,
    ( r1_xboole_0(sK3,sK21(sK2,sK3,sK4))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5078,f4897])).

fof(f5078,plain,
    ( r1_xboole_0(sK3,sK21(sK2,sK3,sK4))
    | ~ r2_hidden(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1 ),
    inference(resolution,[],[f2867,f2824])).

fof(f2824,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k2_pre_topc(X0,X1))
      | r1_xboole_0(X1,sK21(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2424])).

fof(f2424,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r1_xboole_0(X1,sK21(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2196])).

fof(f12396,plain,
    ( ~ r1_xboole_0(sK3,sK21(sK2,sK3,sK4))
    | ~ r2_hidden(sK4,sK21(sK2,sK3,sK4))
    | spl72_1
    | ~ spl72_7
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f12390,f5135])).

fof(f5135,plain,
    ( m1_subset_1(sK21(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5134,f2345])).

fof(f5134,plain,
    ( m1_subset_1(sK21(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5133,f2346])).

fof(f5133,plain,
    ( m1_subset_1(sK21(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5132,f4018])).

fof(f5132,plain,
    ( m1_subset_1(sK21(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5081,f4897])).

fof(f5081,plain,
    ( m1_subset_1(sK21(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1 ),
    inference(resolution,[],[f2867,f2827])).

fof(f2827,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k2_pre_topc(X0,X1))
      | m1_subset_1(sK21(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2421])).

fof(f2421,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_subset_1(sK21(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2196])).

fof(f12390,plain,
    ( ~ m1_subset_1(sK21(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_xboole_0(sK3,sK21(sK2,sK3,sK4))
    | ~ r2_hidden(sK4,sK21(sK2,sK3,sK4))
    | spl72_1
    | ~ spl72_7
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(resolution,[],[f5131,f2894])).

fof(f5131,plain,
    ( v3_pre_topc(sK21(sK2,sK3,sK4),sK2)
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5130,f2345])).

fof(f5130,plain,
    ( v3_pre_topc(sK21(sK2,sK3,sK4),sK2)
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5129,f2346])).

fof(f5129,plain,
    ( v3_pre_topc(sK21(sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_66
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5128,f4018])).

fof(f5128,plain,
    ( v3_pre_topc(sK21(sK2,sK3,sK4),sK2)
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1
    | ~ spl72_120 ),
    inference(subsumption_resolution,[],[f5080,f4897])).

fof(f5080,plain,
    ( v3_pre_topc(sK21(sK2,sK3,sK4),sK2)
    | ~ r2_hidden(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | spl72_1 ),
    inference(resolution,[],[f2867,f2826])).

fof(f2826,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k2_pre_topc(X0,X1))
      | v3_pre_topc(sK21(X0,X1,X6),X0)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2422])).

fof(f2422,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | v3_pre_topc(sK21(X0,X1,X6),X0)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2196])).

fof(f6220,plain,
    ( spl72_36
    | ~ spl72_123 ),
    inference(avatar_split_clause,[],[f6206,f4912,f3416])).

fof(f4912,plain,
    ( spl72_123
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_123])])).

fof(f6206,plain,
    ( k1_xboole_0 = sK3
    | ~ spl72_123 ),
    inference(resolution,[],[f4914,f2664])).

fof(f4914,plain,
    ( v1_xboole_0(sK3)
    | ~ spl72_123 ),
    inference(avatar_component_clause,[],[f4912])).

fof(f4917,plain,
    ( ~ spl72_2
    | spl72_119 ),
    inference(avatar_split_clause,[],[f3085,f4891,f2869])).

fof(f2869,plain,
    ( spl72_2
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl72_2])])).

fof(f3085,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v2_struct_0(sK2) ),
    inference(resolution,[],[f2958,f2437])).

fof(f2437,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1912])).

fof(f1912,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f1911])).

fof(f1911,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1791])).

fof(f1791,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f2958,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f2345,f2798])).

fof(f2798,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2132])).

fof(f2132,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1780])).

fof(f1780,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f4916,plain,
    ( spl72_2
    | ~ spl72_119 ),
    inference(avatar_split_clause,[],[f3088,f4891,f2869])).

fof(f3088,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f2958,f2440])).

fof(f2440,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1916])).

fof(f1916,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1915])).

fof(f1915,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1793])).

fof(f1793,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f4915,plain,
    ( ~ spl72_119
    | spl72_123 ),
    inference(avatar_split_clause,[],[f3219,f4912,f4891])).

fof(f3219,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f2346,f2662])).

fof(f4904,plain,
    ( spl72_119
    | spl72_120 ),
    inference(avatar_split_clause,[],[f3073,f4895,f4891])).

fof(f3073,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f2347,f2648])).

fof(f2648,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2043])).

fof(f2043,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f2042])).

fof(f2042,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f2347,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f2167])).

fof(f4067,plain,(
    spl72_66 ),
    inference(avatar_split_clause,[],[f3375,f4017])).

fof(f3375,plain,(
    m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f3140,f2345])).

fof(f3140,plain,
    ( m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f2346,f2452])).

fof(f2452,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1928])).

fof(f1928,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1927])).

fof(f1927,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1778])).

fof(f1778,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f3966,plain,
    ( spl72_55
    | spl72_56
    | ~ spl72_27 ),
    inference(avatar_split_clause,[],[f3957,f3077,f3963,f3959])).

fof(f3957,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(k1_tarski(k1_xboole_0)))
    | ~ spl72_27 ),
    inference(forward_demodulation,[],[f3956,f2575])).

fof(f3956,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(k1_tarski(k1_xboole_0)))
    | ~ spl72_27 ),
    inference(forward_demodulation,[],[f3955,f3079])).

fof(f3955,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(k1_tarski(k1_xboole_0)))
    | k1_xboole_0 = k1_zfmisc_1(u1_struct_0(sK2))
    | ~ spl72_27 ),
    inference(forward_demodulation,[],[f3954,f2575])).

fof(f3954,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | k1_xboole_0 = k1_zfmisc_1(u1_struct_0(sK2))
    | ~ spl72_27 ),
    inference(forward_demodulation,[],[f3280,f3079])).

fof(f3280,plain,
    ( m1_subset_1(k1_tarski(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | k1_xboole_0 = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(resolution,[],[f2346,f2570])).

fof(f2570,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f1996])).

fof(f1996,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f1995])).

fof(f1995,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f527])).

fof(f527,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f2896,plain,
    ( spl72_1
    | ~ spl72_2 ),
    inference(avatar_split_clause,[],[f2348,f2869,f2865])).

fof(f2348,plain,
    ( ~ v2_struct_0(sK2)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f2167])).

fof(f2895,plain,
    ( spl72_1
    | spl72_7 ),
    inference(avatar_split_clause,[],[f2349,f2893,f2865])).

fof(f2349,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(sK3,X4)
      | ~ r2_hidden(sK4,X4)
      | ~ v3_pre_topc(X4,sK2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ) ),
    inference(cnf_transformation,[],[f2167])).

fof(f2891,plain,
    ( ~ spl72_1
    | spl72_2
    | spl72_6 ),
    inference(avatar_split_clause,[],[f2350,f2888,f2869,f2865])).

fof(f2350,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f2167])).

fof(f2886,plain,
    ( ~ spl72_1
    | spl72_2
    | spl72_5 ),
    inference(avatar_split_clause,[],[f2351,f2883,f2869,f2865])).

fof(f2351,plain,
    ( v3_pre_topc(sK5,sK2)
    | v2_struct_0(sK2)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f2167])).

fof(f2881,plain,
    ( ~ spl72_1
    | spl72_2
    | spl72_4 ),
    inference(avatar_split_clause,[],[f2352,f2878,f2869,f2865])).

fof(f2352,plain,
    ( r2_hidden(sK4,sK5)
    | v2_struct_0(sK2)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f2167])).

fof(f2876,plain,
    ( ~ spl72_1
    | spl72_2
    | spl72_3 ),
    inference(avatar_split_clause,[],[f2353,f2873,f2869,f2865])).

fof(f2353,plain,
    ( r1_xboole_0(sK3,sK5)
    | v2_struct_0(sK2)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f2167])).
%------------------------------------------------------------------------------
