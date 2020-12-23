%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  173 (4779 expanded)
%              Number of leaves         :   20 (1764 expanded)
%              Depth                    :   31
%              Number of atoms          :  886 (49069 expanded)
%              Number of equality atoms :   62 ( 235 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f390,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f79,f165,f188,f261,f269,f270,f292,f318,f383,f389])).

fof(f389,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f387,f368])).

fof(f368,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f177,f358])).

fof(f358,plain,
    ( k1_xboole_0 = sK2
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f357,f177])).

fof(f357,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2)
    | spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f356,f177])).

fof(f356,plain,(
    ! [X1] :
      ( ~ m1_orders_2(sK2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,sK0,sK2) ) ),
    inference(subsumption_resolution,[],[f118,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f112,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f33,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,sK0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,sK0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,sK0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,sK0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_orders_2(X2,sK0,X3)
              | ~ r2_xboole_0(X2,X3) )
            & ( m1_orders_2(X2,sK0,X3)
              | r2_xboole_0(X2,X3) )
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ( ~ m1_orders_2(sK2,sK0,X3)
            | ~ r2_xboole_0(sK2,X3) )
          & ( m1_orders_2(sK2,sK0,X3)
            | r2_xboole_0(sK2,X3) )
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ( ~ m1_orders_2(sK2,sK0,X3)
          | ~ r2_xboole_0(sK2,X3) )
        & ( m1_orders_2(sK2,sK0,X3)
          | r2_xboole_0(sK2,X3) )
        & m2_orders_2(X3,sK0,sK1) )
   => ( ( ~ m1_orders_2(sK2,sK0,sK3)
        | ~ r2_xboole_0(sK2,sK3) )
      & ( m1_orders_2(sK2,sK0,sK3)
        | r2_xboole_0(sK2,sK3) )
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

fof(f112,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f111,f42])).

fof(f42,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f110,f43])).

fof(f43,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f44])).

fof(f44,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f106,f45])).

fof(f45,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f104,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f104,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f88,f47])).

fof(f47,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f87,f41])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f42])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f85,f43])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f44])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f45])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f46,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f46,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f118,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f117,f41])).

fof(f117,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f116,f42])).

fof(f116,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f43])).

fof(f115,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f44])).

fof(f114,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f107,f45])).

fof(f107,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f104,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

fof(f177,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f76,f156])).

fof(f156,plain,
    ( sK2 = sK3
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f154,f73])).

fof(f73,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_1
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f154,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f152,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f152,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f141,f76])).

fof(f141,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3) ) ),
    inference(subsumption_resolution,[],[f140,f41])).

fof(f140,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f42])).

fof(f139,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f43])).

fof(f138,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f137,f44])).

fof(f137,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f126,f45])).

fof(f126,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f105,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(f105,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f88,f48])).

fof(f48,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_2
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f387,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(forward_demodulation,[],[f386,f367])).

fof(f367,plain,
    ( k1_xboole_0 = sK3
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f164,f358])).

fof(f164,plain,
    ( sK2 = sK3
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_4
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f386,plain,
    ( ~ m1_orders_2(sK3,sK0,k1_xboole_0)
    | spl4_1
    | ~ spl4_2
    | spl4_5 ),
    inference(forward_demodulation,[],[f173,f358])).

fof(f173,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_5
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f383,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f370,f364])).

fof(f364,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f144,f358])).

fof(f144,plain,(
    ~ r1_xboole_0(sK2,sK2) ),
    inference(resolution,[],[f142,f47])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f103,f47])).

fof(f103,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X6,sK0,sK1)
      | ~ m2_orders_2(X5,sK0,sK1)
      | ~ r1_xboole_0(X6,X5) ) ),
    inference(subsumption_resolution,[],[f102,f41])).

fof(f102,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X5,sK0,sK1)
      | ~ m2_orders_2(X6,sK0,sK1)
      | ~ r1_xboole_0(X6,X5)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f101,f42])).

fof(f101,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X5,sK0,sK1)
      | ~ m2_orders_2(X6,sK0,sK1)
      | ~ r1_xboole_0(X6,X5)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f100,f43])).

fof(f100,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X5,sK0,sK1)
      | ~ m2_orders_2(X6,sK0,sK1)
      | ~ r1_xboole_0(X6,X5)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f99,f44])).

fof(f99,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X5,sK0,sK1)
      | ~ m2_orders_2(X6,sK0,sK1)
      | ~ r1_xboole_0(X6,X5)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f83,f45])).

fof(f83,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X5,sK0,sK1)
      | ~ m2_orders_2(X6,sK0,sK1)
      | ~ r1_xboole_0(X6,X5)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f46,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ r1_xboole_0(X2,X3)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

fof(f370,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f328,f358])).

fof(f328,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f56,f325])).

fof(f325,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f293,f164])).

fof(f293,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f290,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f290,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f172,f123])).

fof(f123,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f122,f41])).

fof(f122,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f121,f42])).

fof(f121,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f43])).

fof(f120,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f44])).

fof(f119,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f108,f45])).

fof(f108,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f104,f54])).

fof(f172,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f171])).

fof(f56,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f318,plain,
    ( ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f306,f69])).

fof(f69,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f306,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f72,f164])).

fof(f72,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f292,plain,
    ( spl4_3
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f290,f160])).

fof(f160,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_3
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f270,plain,
    ( spl4_2
    | spl4_5
    | spl4_4 ),
    inference(avatar_split_clause,[],[f268,f162,f171,f75])).

fof(f268,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(resolution,[],[f48,f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | m1_orders_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f98,f47])).

fof(f98,plain,(
    ! [X4,X3] :
      ( ~ m2_orders_2(X4,sK0,sK1)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,sK1)
      | m1_orders_2(X3,sK0,X4)
      | m1_orders_2(X4,sK0,X3) ) ),
    inference(subsumption_resolution,[],[f97,f41])).

fof(f97,plain,(
    ! [X4,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,sK1)
      | ~ m2_orders_2(X4,sK0,sK1)
      | m1_orders_2(X4,sK0,X3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f96,f42])).

fof(f96,plain,(
    ! [X4,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,sK1)
      | ~ m2_orders_2(X4,sK0,sK1)
      | m1_orders_2(X4,sK0,X3)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f43])).

fof(f95,plain,(
    ! [X4,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,sK1)
      | ~ m2_orders_2(X4,sK0,sK1)
      | m1_orders_2(X4,sK0,X3)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f44])).

fof(f94,plain,(
    ! [X4,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,sK1)
      | ~ m2_orders_2(X4,sK0,sK1)
      | m1_orders_2(X4,sK0,X3)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f82,f45])).

fof(f82,plain,(
    ! [X4,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,sK1)
      | ~ m2_orders_2(X4,sK0,sK1)
      | m1_orders_2(X4,sK0,X3)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f46,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | m1_orders_2(X2,X0,X3)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

fof(f269,plain,
    ( ~ spl4_2
    | spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f267,f171,f162,f75])).

fof(f267,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | sK2 = sK3
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(resolution,[],[f48,f146])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X0,sK0,sK2)
      | sK2 = X0
      | ~ m1_orders_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f93,f47])).

fof(f93,plain,(
    ! [X2,X1] :
      ( ~ m2_orders_2(X2,sK0,sK1)
      | X1 = X2
      | ~ m1_orders_2(X1,sK0,X2)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m1_orders_2(X2,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f92,f41])).

fof(f92,plain,(
    ! [X2,X1] :
      ( ~ m1_orders_2(X1,sK0,X2)
      | X1 = X2
      | ~ m2_orders_2(X2,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m1_orders_2(X2,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f91,f42])).

fof(f91,plain,(
    ! [X2,X1] :
      ( ~ m1_orders_2(X1,sK0,X2)
      | X1 = X2
      | ~ m2_orders_2(X2,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m1_orders_2(X2,sK0,X1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f90,f43])).

fof(f90,plain,(
    ! [X2,X1] :
      ( ~ m1_orders_2(X1,sK0,X2)
      | X1 = X2
      | ~ m2_orders_2(X2,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m1_orders_2(X2,sK0,X1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f89,f44])).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ m1_orders_2(X1,sK0,X2)
      | X1 = X2
      | ~ m2_orders_2(X2,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m1_orders_2(X2,sK0,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f45])).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ m1_orders_2(X1,sK0,X2)
      | X1 = X2
      | ~ m2_orders_2(X2,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m1_orders_2(X2,sK0,X1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f46,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X3)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X3,X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f261,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f260,f71,f162,f158])).

fof(f260,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f190,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f190,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_1 ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f188,plain,
    ( spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f186,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f186,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(forward_demodulation,[],[f160,f156])).

fof(f165,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f155,f75,f162,f158])).

fof(f155,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f152,f61])).

fof(f79,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f49,f75,f71])).

fof(f49,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f50,f75,f71])).

fof(f50,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:29:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (21669)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.46  % (21685)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.46  % (21669)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f390,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f78,f79,f165,f188,f261,f269,f270,f292,f318,f383,f389])).
% 0.20/0.46  fof(f389,plain,(
% 0.20/0.46    spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f388])).
% 0.20/0.46  fof(f388,plain,(
% 0.20/0.46    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f387,f368])).
% 0.20/0.46  fof(f368,plain,(
% 0.20/0.46    m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (spl4_1 | ~spl4_2)),
% 0.20/0.46    inference(backward_demodulation,[],[f177,f358])).
% 0.20/0.46  fof(f358,plain,(
% 0.20/0.46    k1_xboole_0 = sK2 | (spl4_1 | ~spl4_2)),
% 0.20/0.46    inference(subsumption_resolution,[],[f357,f177])).
% 0.20/0.46  fof(f357,plain,(
% 0.20/0.46    k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2) | (spl4_1 | ~spl4_2)),
% 0.20/0.46    inference(resolution,[],[f356,f177])).
% 0.20/0.46  fof(f356,plain,(
% 0.20/0.46    ( ! [X1] : (~m1_orders_2(sK2,sK0,X1) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,sK2)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f118,f113])).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f112,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ~v2_struct_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f33,f32,f31,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f11])).
% 0.20/0.46  fof(f11,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f111,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    v3_orders_2(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f110,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    v4_orders_2(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f109,f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    v5_orders_2(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f106,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    l1_orders_2(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(resolution,[],[f104,f58])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(resolution,[],[f88,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    m2_orders_2(sK2,sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f87,f41])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f86,f42])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f85,f43])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f84,f44])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f80,f45])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(resolution,[],[f46,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.46    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f117,f41])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f116,f42])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f115,f43])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f114,f44])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f107,f45])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(resolution,[],[f104,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    m1_orders_2(sK2,sK0,sK2) | (spl4_1 | ~spl4_2)),
% 0.20/0.47    inference(backward_demodulation,[],[f76,f156])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    sK2 = sK3 | (spl4_1 | ~spl4_2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f154,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ~r2_xboole_0(sK2,sK3) | spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl4_1 <=> r2_xboole_0(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl4_2),
% 0.20/0.47    inference(resolution,[],[f152,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.47    inference(flattening,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.20/0.47    inference(resolution,[],[f141,f76])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f140,f41])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f139,f42])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f138,f43])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f137,f44])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f126,f45])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(resolution,[],[f105,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(resolution,[],[f88,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    m2_orders_2(sK3,sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    m1_orders_2(sK2,sK0,sK3) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl4_2 <=> m1_orders_2(sK2,sK0,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f387,plain,(
% 0.20/0.47    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5)),
% 0.20/0.47    inference(forward_demodulation,[],[f386,f367])).
% 0.20/0.47  fof(f367,plain,(
% 0.20/0.47    k1_xboole_0 = sK3 | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.47    inference(backward_demodulation,[],[f164,f358])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    sK2 = sK3 | ~spl4_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f162])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    spl4_4 <=> sK2 = sK3),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.47  fof(f386,plain,(
% 0.20/0.47    ~m1_orders_2(sK3,sK0,k1_xboole_0) | (spl4_1 | ~spl4_2 | spl4_5)),
% 0.20/0.47    inference(forward_demodulation,[],[f173,f358])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    ~m1_orders_2(sK3,sK0,sK2) | spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f171])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    spl4_5 <=> m1_orders_2(sK3,sK0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f383,plain,(
% 0.20/0.47    spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f382])).
% 0.20/0.47  fof(f382,plain,(
% 0.20/0.47    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5)),
% 0.20/0.47    inference(subsumption_resolution,[],[f370,f364])).
% 0.20/0.47  fof(f364,plain,(
% 0.20/0.47    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl4_1 | ~spl4_2)),
% 0.20/0.47    inference(backward_demodulation,[],[f144,f358])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ~r1_xboole_0(sK2,sK2)),
% 0.20/0.47    inference(resolution,[],[f142,f47])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(sK2,X0)) )),
% 0.20/0.47    inference(resolution,[],[f103,f47])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ( ! [X6,X5] : (~m2_orders_2(X6,sK0,sK1) | ~m2_orders_2(X5,sK0,sK1) | ~r1_xboole_0(X6,X5)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f102,f41])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ( ! [X6,X5] : (~m2_orders_2(X5,sK0,sK1) | ~m2_orders_2(X6,sK0,sK1) | ~r1_xboole_0(X6,X5) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f101,f42])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    ( ! [X6,X5] : (~m2_orders_2(X5,sK0,sK1) | ~m2_orders_2(X6,sK0,sK1) | ~r1_xboole_0(X6,X5) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f100,f43])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X6,X5] : (~m2_orders_2(X5,sK0,sK1) | ~m2_orders_2(X6,sK0,sK1) | ~r1_xboole_0(X6,X5) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f99,f44])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X6,X5] : (~m2_orders_2(X5,sK0,sK1) | ~m2_orders_2(X6,sK0,sK1) | ~r1_xboole_0(X6,X5) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f83,f45])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ( ! [X6,X5] : (~m2_orders_2(X5,sK0,sK1) | ~m2_orders_2(X6,sK0,sK1) | ~r1_xboole_0(X6,X5) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(resolution,[],[f46,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~r1_xboole_0(X2,X3) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).
% 0.20/0.47  fof(f370,plain,(
% 0.20/0.47    r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5)),
% 0.20/0.47    inference(backward_demodulation,[],[f328,f358])).
% 0.20/0.47  fof(f328,plain,(
% 0.20/0.47    r1_xboole_0(k1_xboole_0,sK2) | (~spl4_4 | ~spl4_5)),
% 0.20/0.47    inference(superposition,[],[f56,f325])).
% 0.20/0.47  fof(f325,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK2,sK2) | (~spl4_4 | ~spl4_5)),
% 0.20/0.47    inference(forward_demodulation,[],[f293,f164])).
% 0.20/0.47  fof(f293,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK3,sK2) | ~spl4_5),
% 0.20/0.47    inference(resolution,[],[f290,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.47    inference(nnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.47  fof(f290,plain,(
% 0.20/0.47    r1_tarski(sK3,sK2) | ~spl4_5),
% 0.20/0.47    inference(resolution,[],[f172,f123])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f122,f41])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f121,f42])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f120,f43])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f119,f44])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f108,f45])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(resolution,[],[f104,f54])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    m1_orders_2(sK3,sK0,sK2) | ~spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f171])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.47  fof(f318,plain,(
% 0.20/0.47    ~spl4_1 | ~spl4_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f317])).
% 0.20/0.47  fof(f317,plain,(
% 0.20/0.47    $false | (~spl4_1 | ~spl4_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f306,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f306,plain,(
% 0.20/0.47    r2_xboole_0(sK2,sK2) | (~spl4_1 | ~spl4_4)),
% 0.20/0.47    inference(backward_demodulation,[],[f72,f164])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    r2_xboole_0(sK2,sK3) | ~spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f71])).
% 0.20/0.47  fof(f292,plain,(
% 0.20/0.47    spl4_3 | ~spl4_5),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f291])).
% 0.20/0.47  fof(f291,plain,(
% 0.20/0.47    $false | (spl4_3 | ~spl4_5)),
% 0.20/0.47    inference(subsumption_resolution,[],[f290,f160])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    ~r1_tarski(sK3,sK2) | spl4_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f158])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    spl4_3 <=> r1_tarski(sK3,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f270,plain,(
% 0.20/0.47    spl4_2 | spl4_5 | spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f268,f162,f171,f75])).
% 0.20/0.47  fof(f268,plain,(
% 0.20/0.47    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3)),
% 0.20/0.47    inference(resolution,[],[f48,f150])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) )),
% 0.20/0.47    inference(resolution,[],[f98,f47])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X4,X3] : (~m2_orders_2(X4,sK0,sK1) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | m1_orders_2(X3,sK0,X4) | m1_orders_2(X4,sK0,X3)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f97,f41])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ( ! [X4,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | ~m2_orders_2(X4,sK0,sK1) | m1_orders_2(X4,sK0,X3) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f96,f42])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    ( ! [X4,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | ~m2_orders_2(X4,sK0,sK1) | m1_orders_2(X4,sK0,X3) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f95,f43])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ( ! [X4,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | ~m2_orders_2(X4,sK0,sK1) | m1_orders_2(X4,sK0,X3) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f94,f44])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ( ! [X4,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | ~m2_orders_2(X4,sK0,sK1) | m1_orders_2(X4,sK0,X3) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f82,f45])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ( ! [X4,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | ~m2_orders_2(X4,sK0,sK1) | m1_orders_2(X4,sK0,X3) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(resolution,[],[f46,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | m1_orders_2(X2,X0,X3) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).
% 0.20/0.47  fof(f269,plain,(
% 0.20/0.47    ~spl4_2 | spl4_4 | ~spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f267,f171,f162,f75])).
% 0.20/0.47  fof(f267,plain,(
% 0.20/0.47    ~m1_orders_2(sK3,sK0,sK2) | sK2 = sK3 | ~m1_orders_2(sK2,sK0,sK3)),
% 0.20/0.47    inference(resolution,[],[f48,f146])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X0,sK0,sK2) | sK2 = X0 | ~m1_orders_2(sK2,sK0,X0)) )),
% 0.20/0.47    inference(resolution,[],[f93,f47])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~m2_orders_2(X2,sK0,sK1) | X1 = X2 | ~m1_orders_2(X1,sK0,X2) | ~m2_orders_2(X1,sK0,sK1) | ~m1_orders_2(X2,sK0,X1)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f92,f41])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~m1_orders_2(X1,sK0,X2) | X1 = X2 | ~m2_orders_2(X2,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~m1_orders_2(X2,sK0,X1) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f91,f42])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~m1_orders_2(X1,sK0,X2) | X1 = X2 | ~m2_orders_2(X2,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~m1_orders_2(X2,sK0,X1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f90,f43])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~m1_orders_2(X1,sK0,X2) | X1 = X2 | ~m2_orders_2(X2,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~m1_orders_2(X2,sK0,X1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f89,f44])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~m1_orders_2(X1,sK0,X2) | X1 = X2 | ~m2_orders_2(X2,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~m1_orders_2(X2,sK0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f81,f45])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~m1_orders_2(X1,sK0,X2) | X1 = X2 | ~m2_orders_2(X2,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~m1_orders_2(X2,sK0,X1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(resolution,[],[f46,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_2(X3,X0,X2) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f261,plain,(
% 0.20/0.47    ~spl4_3 | spl4_4 | ~spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f260,f71,f162,f158])).
% 0.20/0.47  fof(f260,plain,(
% 0.20/0.47    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f190,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.47    inference(flattening,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    r1_tarski(sK2,sK3) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f72,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    spl4_1 | ~spl4_2 | spl4_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f187])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    $false | (spl4_1 | ~spl4_2 | spl4_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f186,f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    ~r1_tarski(sK2,sK2) | (spl4_1 | ~spl4_2 | spl4_3)),
% 0.20/0.47    inference(forward_demodulation,[],[f160,f156])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    ~spl4_3 | spl4_4 | ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f155,f75,f162,f158])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl4_2),
% 0.20/0.47    inference(resolution,[],[f152,f61])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl4_1 | spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f49,f75,f71])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ~spl4_1 | ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f50,f75,f71])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (21669)------------------------------
% 0.20/0.47  % (21669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (21669)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (21669)Memory used [KB]: 10746
% 0.20/0.47  % (21669)Time elapsed: 0.079 s
% 0.20/0.47  % (21669)------------------------------
% 0.20/0.47  % (21669)------------------------------
% 0.20/0.47  % (21666)Success in time 0.119 s
%------------------------------------------------------------------------------
