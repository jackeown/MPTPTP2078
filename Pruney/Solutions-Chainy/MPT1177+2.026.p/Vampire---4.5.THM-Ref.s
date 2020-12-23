%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  175 (3997 expanded)
%              Number of leaves         :   21 (1469 expanded)
%              Depth                    :   31
%              Number of atoms          :  854 (40727 expanded)
%              Number of equality atoms :   56 ( 204 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f663,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f83,f169,f192,f414,f421,f451,f480,f615,f662])).

fof(f662,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f661])).

fof(f661,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f660,f602])).

fof(f602,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f181,f589])).

fof(f589,plain,
    ( k1_xboole_0 = sK2
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f588,f181])).

fof(f588,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2)
    | spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f585,f181])).

fof(f585,plain,(
    ! [X1] :
      ( ~ m1_orders_2(sK2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,sK0,sK2) ) ),
    inference(subsumption_resolution,[],[f122,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f116,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f35,f34,f33,f32])).

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f44])).

fof(f44,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f45,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f46])).

fof(f46,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f110,f47])).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f108,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f108,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f92,f49])).

fof(f49,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f91,f43])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f90,f44])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f88,f46])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f47])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f48,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
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

fof(f48,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f122,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f121,f43])).

fof(f121,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f44])).

fof(f120,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f45])).

fof(f119,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f46])).

fof(f118,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f111,f47])).

fof(f111,plain,(
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
    inference(resolution,[],[f108,f57])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f181,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f80,f160])).

fof(f160,plain,
    ( sK2 = sK3
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f158,f77])).

fof(f77,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_1
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f158,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f156,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f156,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f145,f80])).

fof(f145,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3) ) ),
    inference(subsumption_resolution,[],[f144,f43])).

fof(f144,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f44])).

fof(f143,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f45])).

fof(f142,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f141,f46])).

fof(f141,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f130,f47])).

fof(f130,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK3)
      | r1_tarski(X2,sK3)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f109,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(f109,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f92,f50])).

fof(f50,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_2
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f660,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(forward_demodulation,[],[f628,f601])).

fof(f601,plain,
    ( k1_xboole_0 = sK3
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f168,f589])).

fof(f168,plain,
    ( sK2 = sK3
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl4_4
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f628,plain,
    ( ~ m1_orders_2(sK3,sK0,k1_xboole_0)
    | spl4_1
    | ~ spl4_2
    | spl4_5 ),
    inference(forward_demodulation,[],[f177,f589])).

fof(f177,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_5
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f615,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f614])).

fof(f614,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f598,f539])).

fof(f539,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f533,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f533,plain,
    ( ! [X5] : r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f58,f506])).

fof(f506,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK2)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f503,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

fof(f503,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k1_xboole_0,X0),sK2)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f492,f58])).

fof(f492,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | r1_tarski(X0,sK2) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f69,f491])).

fof(f491,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f457,f168])).

fof(f457,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f449,f68])).

fof(f449,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f176,f127])).

fof(f127,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f126,f43])).

fof(f126,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f125,f44])).

fof(f125,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f124,f45])).

fof(f124,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f123,f46])).

fof(f123,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f112,f47])).

fof(f112,plain,(
    ! [X2] :
      ( ~ m1_orders_2(X2,sK0,sK2)
      | r1_tarski(X2,sK2)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f108,f56])).

fof(f176,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f175])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f598,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f148,f589])).

fof(f148,plain,(
    ~ r1_xboole_0(sK2,sK2) ),
    inference(resolution,[],[f146,f49])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f107,f49])).

fof(f107,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X6,sK0,sK1)
      | ~ m2_orders_2(X5,sK0,sK1)
      | ~ r1_xboole_0(X6,X5) ) ),
    inference(subsumption_resolution,[],[f106,f43])).

fof(f106,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X5,sK0,sK1)
      | ~ m2_orders_2(X6,sK0,sK1)
      | ~ r1_xboole_0(X6,X5)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f105,f44])).

fof(f105,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X5,sK0,sK1)
      | ~ m2_orders_2(X6,sK0,sK1)
      | ~ r1_xboole_0(X6,X5)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X5,sK0,sK1)
      | ~ m2_orders_2(X6,sK0,sK1)
      | ~ r1_xboole_0(X6,X5)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f103,f46])).

fof(f103,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X5,sK0,sK1)
      | ~ m2_orders_2(X6,sK0,sK1)
      | ~ r1_xboole_0(X6,X5)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f47])).

fof(f87,plain,(
    ! [X6,X5] :
      ( ~ m2_orders_2(X5,sK0,sK1)
      | ~ m2_orders_2(X6,sK0,sK1)
      | ~ r1_xboole_0(X6,X5)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f48,f53])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

fof(f480,plain,
    ( ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f467,f73])).

fof(f73,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f467,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f76,f168])).

fof(f76,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f451,plain,
    ( spl4_3
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f449,f164])).

fof(f164,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_3
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f421,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f420,f75,f166,f162])).

fof(f420,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f194,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f194,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_1 ),
    inference(resolution,[],[f76,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f414,plain,
    ( spl4_2
    | spl4_3
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl4_2
    | spl4_3
    | spl4_5 ),
    inference(subsumption_resolution,[],[f400,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f400,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl4_2
    | spl4_3
    | spl4_5 ),
    inference(backward_demodulation,[],[f164,f389])).

fof(f389,plain,
    ( sK2 = sK3
    | spl4_2
    | spl4_5 ),
    inference(subsumption_resolution,[],[f388,f81])).

fof(f81,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f388,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f385,f177])).

fof(f385,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(resolution,[],[f154,f50])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | m1_orders_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f102,f49])).

fof(f102,plain,(
    ! [X4,X3] :
      ( ~ m2_orders_2(X4,sK0,sK1)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,sK1)
      | m1_orders_2(X3,sK0,X4)
      | m1_orders_2(X4,sK0,X3) ) ),
    inference(subsumption_resolution,[],[f101,f43])).

fof(f101,plain,(
    ! [X4,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,sK1)
      | ~ m2_orders_2(X4,sK0,sK1)
      | m1_orders_2(X4,sK0,X3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f100,f44])).

fof(f100,plain,(
    ! [X4,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,sK1)
      | ~ m2_orders_2(X4,sK0,sK1)
      | m1_orders_2(X4,sK0,X3)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f99,f45])).

fof(f99,plain,(
    ! [X4,X3] :
      ( m1_orders_2(X3,sK0,X4)
      | X3 = X4
      | ~ m2_orders_2(X3,sK0,sK1)
      | ~ m2_orders_2(X4,sK0,sK1)
      | m1_orders_2(X4,sK0,X3)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f46])).

fof(f98,plain,(
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
    inference(subsumption_resolution,[],[f86,f47])).

fof(f86,plain,(
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
    inference(resolution,[],[f48,f55])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f192,plain,
    ( spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f190,f72])).

fof(f190,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(forward_demodulation,[],[f164,f160])).

fof(f169,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f159,f79,f166,f162])).

fof(f159,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f156,f63])).

fof(f83,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f51,f79,f75])).

fof(f51,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f52,f79,f75])).

fof(f52,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:04:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (14463)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (14471)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (14462)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (14468)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (14480)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (14470)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (14460)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (14461)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (14470)Refutation not found, incomplete strategy% (14470)------------------------------
% 0.21/0.52  % (14470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14465)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (14470)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14470)Memory used [KB]: 10618
% 0.21/0.52  % (14470)Time elapsed: 0.102 s
% 0.21/0.52  % (14470)------------------------------
% 0.21/0.52  % (14470)------------------------------
% 0.21/0.52  % (14459)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (14465)Refutation not found, incomplete strategy% (14465)------------------------------
% 0.21/0.52  % (14465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14465)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14465)Memory used [KB]: 10618
% 0.21/0.52  % (14465)Time elapsed: 0.114 s
% 0.21/0.52  % (14465)------------------------------
% 0.21/0.52  % (14465)------------------------------
% 0.21/0.52  % (14460)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (14476)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (14481)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (14483)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (14464)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (14469)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (14473)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (14464)Refutation not found, incomplete strategy% (14464)------------------------------
% 0.21/0.53  % (14464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14474)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (14464)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14464)Memory used [KB]: 6140
% 0.21/0.53  % (14464)Time elapsed: 0.094 s
% 0.21/0.53  % (14464)------------------------------
% 0.21/0.53  % (14464)------------------------------
% 0.21/0.53  % (14475)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (14478)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (14472)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (14477)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (14466)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (14459)Refutation not found, incomplete strategy% (14459)------------------------------
% 0.21/0.54  % (14459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14459)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14459)Memory used [KB]: 10618
% 0.21/0.54  % (14459)Time elapsed: 0.134 s
% 0.21/0.54  % (14459)------------------------------
% 0.21/0.54  % (14459)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f663,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f82,f83,f169,f192,f414,f421,f451,f480,f615,f662])).
% 0.21/0.54  fof(f662,plain,(
% 0.21/0.54    spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f661])).
% 0.21/0.54  fof(f661,plain,(
% 0.21/0.54    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f660,f602])).
% 0.21/0.54  fof(f602,plain,(
% 0.21/0.54    m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (spl4_1 | ~spl4_2)),
% 0.21/0.54    inference(backward_demodulation,[],[f181,f589])).
% 0.21/0.54  fof(f589,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | (spl4_1 | ~spl4_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f588,f181])).
% 0.21/0.54  fof(f588,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2) | (spl4_1 | ~spl4_2)),
% 0.21/0.54    inference(resolution,[],[f585,f181])).
% 0.21/0.54  fof(f585,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_orders_2(sK2,sK0,X1) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,sK2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f122,f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f116,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f35,f34,f33,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f115,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    v3_orders_2(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f114,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    v4_orders_2(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f113,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    v5_orders_2(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f110,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    l1_orders_2(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f108,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(resolution,[],[f92,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    m2_orders_2(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f91,f43])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f90,f44])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f89,f45])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f88,f46])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f84,f47])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f48,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f121,f43])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f120,f44])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f119,f45])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f118,f46])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f111,f47])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_orders_2(X1,sK0,sK2) | k1_xboole_0 = X1 | ~m1_orders_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f108,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    m1_orders_2(sK2,sK0,sK2) | (spl4_1 | ~spl4_2)),
% 0.21/0.54    inference(backward_demodulation,[],[f80,f160])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    sK2 = sK3 | (spl4_1 | ~spl4_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f158,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ~r2_xboole_0(sK2,sK3) | spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl4_1 <=> r2_xboole_0(sK2,sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f156,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.54    inference(flattening,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f145,f80])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f144,f43])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f143,f44])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f142,f45])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f141,f46])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f130,f47])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK3) | r1_tarski(X2,sK3) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f109,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(resolution,[],[f92,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    m2_orders_2(sK3,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    m1_orders_2(sK2,sK0,sK3) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    spl4_2 <=> m1_orders_2(sK2,sK0,sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f660,plain,(
% 0.21/0.54    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5)),
% 0.21/0.54    inference(forward_demodulation,[],[f628,f601])).
% 0.21/0.54  fof(f601,plain,(
% 0.21/0.54    k1_xboole_0 = sK3 | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.54    inference(backward_demodulation,[],[f168,f589])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    sK2 = sK3 | ~spl4_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f166])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    spl4_4 <=> sK2 = sK3),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f628,plain,(
% 0.21/0.54    ~m1_orders_2(sK3,sK0,k1_xboole_0) | (spl4_1 | ~spl4_2 | spl4_5)),
% 0.21/0.54    inference(forward_demodulation,[],[f177,f589])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    ~m1_orders_2(sK3,sK0,sK2) | spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f175])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    spl4_5 <=> m1_orders_2(sK3,sK0,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f615,plain,(
% 0.21/0.54    spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f614])).
% 0.21/0.54  fof(f614,plain,(
% 0.21/0.54    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f598,f539])).
% 0.21/0.54  fof(f539,plain,(
% 0.21/0.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_5)),
% 0.21/0.54    inference(resolution,[],[f533,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.54  fof(f533,plain,(
% 0.21/0.54    ( ! [X5] : (r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5))) ) | (~spl4_4 | ~spl4_5)),
% 0.21/0.54    inference(superposition,[],[f58,f506])).
% 0.21/0.54  fof(f506,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK2)) ) | (~spl4_4 | ~spl4_5)),
% 0.21/0.54    inference(resolution,[],[f503,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.54    inference(nnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.54  fof(f503,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k4_xboole_0(k1_xboole_0,X0),sK2)) ) | (~spl4_4 | ~spl4_5)),
% 0.21/0.54    inference(resolution,[],[f492,f58])).
% 0.21/0.54  fof(f492,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,sK2)) ) | (~spl4_4 | ~spl4_5)),
% 0.21/0.54    inference(superposition,[],[f69,f491])).
% 0.21/0.54  fof(f491,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(sK2,sK2) | (~spl4_4 | ~spl4_5)),
% 0.21/0.54    inference(forward_demodulation,[],[f457,f168])).
% 0.21/0.54  fof(f457,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(sK3,sK2) | ~spl4_5),
% 0.21/0.54    inference(resolution,[],[f449,f68])).
% 0.21/0.54  fof(f449,plain,(
% 0.21/0.54    r1_tarski(sK3,sK2) | ~spl4_5),
% 0.21/0.54    inference(resolution,[],[f176,f127])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f126,f43])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f125,f44])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f124,f45])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f123,f46])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f112,f47])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_orders_2(X2,sK0,sK2) | r1_tarski(X2,sK2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f108,f56])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    m1_orders_2(sK3,sK0,sK2) | ~spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f175])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.54  fof(f598,plain,(
% 0.21/0.54    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl4_1 | ~spl4_2)),
% 0.21/0.54    inference(backward_demodulation,[],[f148,f589])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ~r1_xboole_0(sK2,sK2)),
% 0.21/0.54    inference(resolution,[],[f146,f49])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(sK2,X0)) )),
% 0.21/0.54    inference(resolution,[],[f107,f49])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X6,X5] : (~m2_orders_2(X6,sK0,sK1) | ~m2_orders_2(X5,sK0,sK1) | ~r1_xboole_0(X6,X5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f106,f43])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X6,X5] : (~m2_orders_2(X5,sK0,sK1) | ~m2_orders_2(X6,sK0,sK1) | ~r1_xboole_0(X6,X5) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f105,f44])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ( ! [X6,X5] : (~m2_orders_2(X5,sK0,sK1) | ~m2_orders_2(X6,sK0,sK1) | ~r1_xboole_0(X6,X5) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f104,f45])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X6,X5] : (~m2_orders_2(X5,sK0,sK1) | ~m2_orders_2(X6,sK0,sK1) | ~r1_xboole_0(X6,X5) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f103,f46])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X6,X5] : (~m2_orders_2(X5,sK0,sK1) | ~m2_orders_2(X6,sK0,sK1) | ~r1_xboole_0(X6,X5) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f87,f47])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X6,X5] : (~m2_orders_2(X5,sK0,sK1) | ~m2_orders_2(X6,sK0,sK1) | ~r1_xboole_0(X6,X5) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f48,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~r1_xboole_0(X2,X3) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).
% 0.21/0.54  fof(f480,plain,(
% 0.21/0.54    ~spl4_1 | ~spl4_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f479])).
% 0.21/0.54  fof(f479,plain,(
% 0.21/0.54    $false | (~spl4_1 | ~spl4_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f467,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f467,plain,(
% 0.21/0.54    r2_xboole_0(sK2,sK2) | (~spl4_1 | ~spl4_4)),
% 0.21/0.54    inference(backward_demodulation,[],[f76,f168])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    r2_xboole_0(sK2,sK3) | ~spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f75])).
% 0.21/0.54  fof(f451,plain,(
% 0.21/0.54    spl4_3 | ~spl4_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f450])).
% 0.21/0.54  fof(f450,plain,(
% 0.21/0.54    $false | (spl4_3 | ~spl4_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f449,f164])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ~r1_tarski(sK3,sK2) | spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f162])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    spl4_3 <=> r1_tarski(sK3,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f421,plain,(
% 0.21/0.54    ~spl4_3 | spl4_4 | ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f420,f75,f166,f162])).
% 0.21/0.54  fof(f420,plain,(
% 0.21/0.54    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f194,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    r1_tarski(sK2,sK3) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f76,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f414,plain,(
% 0.21/0.54    spl4_2 | spl4_3 | spl4_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f413])).
% 0.21/0.54  fof(f413,plain,(
% 0.21/0.54    $false | (spl4_2 | spl4_3 | spl4_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f400,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f400,plain,(
% 0.21/0.54    ~r1_tarski(sK2,sK2) | (spl4_2 | spl4_3 | spl4_5)),
% 0.21/0.54    inference(backward_demodulation,[],[f164,f389])).
% 0.21/0.54  fof(f389,plain,(
% 0.21/0.54    sK2 = sK3 | (spl4_2 | spl4_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f388,f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ~m1_orders_2(sK2,sK0,sK3) | spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f79])).
% 0.21/0.54  fof(f388,plain,(
% 0.21/0.54    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | spl4_5),
% 0.21/0.54    inference(subsumption_resolution,[],[f385,f177])).
% 0.21/0.54  fof(f385,plain,(
% 0.21/0.54    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3)),
% 0.21/0.54    inference(resolution,[],[f154,f50])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f102,f49])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~m2_orders_2(X4,sK0,sK1) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | m1_orders_2(X3,sK0,X4) | m1_orders_2(X4,sK0,X3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f101,f43])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X4,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | ~m2_orders_2(X4,sK0,sK1) | m1_orders_2(X4,sK0,X3) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f100,f44])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X4,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | ~m2_orders_2(X4,sK0,sK1) | m1_orders_2(X4,sK0,X3) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f99,f45])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X4,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | ~m2_orders_2(X4,sK0,sK1) | m1_orders_2(X4,sK0,X3) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f98,f46])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X4,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | ~m2_orders_2(X4,sK0,sK1) | m1_orders_2(X4,sK0,X3) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f86,f47])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X4,X3] : (m1_orders_2(X3,sK0,X4) | X3 = X4 | ~m2_orders_2(X3,sK0,sK1) | ~m2_orders_2(X4,sK0,sK1) | m1_orders_2(X4,sK0,X3) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f48,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | m1_orders_2(X2,X0,X3) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).
% 0.21/0.54  fof(f192,plain,(
% 0.21/0.54    spl4_1 | ~spl4_2 | spl4_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    $false | (spl4_1 | ~spl4_2 | spl4_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f190,f72])).
% 0.21/0.54  fof(f190,plain,(
% 0.21/0.54    ~r1_tarski(sK2,sK2) | (spl4_1 | ~spl4_2 | spl4_3)),
% 0.21/0.54    inference(forward_demodulation,[],[f164,f160])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    ~spl4_3 | spl4_4 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f159,f79,f166,f162])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f156,f63])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    spl4_1 | spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f51,f79,f75])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ~spl4_1 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f52,f79,f75])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (14460)------------------------------
% 0.21/0.54  % (14460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14460)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (14460)Memory used [KB]: 10746
% 0.21/0.54  % (14460)Time elapsed: 0.108 s
% 0.21/0.54  % (14460)------------------------------
% 0.21/0.54  % (14460)------------------------------
% 0.21/0.54  % (14472)Refutation not found, incomplete strategy% (14472)------------------------------
% 0.21/0.54  % (14472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14472)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14472)Memory used [KB]: 6140
% 0.21/0.54  % (14472)Time elapsed: 0.109 s
% 0.21/0.54  % (14472)------------------------------
% 0.21/0.54  % (14472)------------------------------
% 0.21/0.55  % (14458)Success in time 0.183 s
%------------------------------------------------------------------------------
