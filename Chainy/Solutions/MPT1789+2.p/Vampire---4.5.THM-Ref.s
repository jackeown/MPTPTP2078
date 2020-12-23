%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1789+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:32 EST 2020

% Result     : Theorem 7.55s
% Output     : Refutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 172 expanded)
%              Number of leaves         :   18 (  75 expanded)
%              Depth                    :    7
%              Number of atoms          :  277 ( 629 expanded)
%              Number of equality atoms :   50 ( 138 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9200,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4963,f4968,f4973,f4983,f5002,f5130,f5140,f5329,f5416,f9163,f9165])).

fof(f9165,plain,
    ( spl172_9
    | ~ spl172_28
    | ~ spl172_30
    | ~ spl172_43
    | ~ spl172_49 ),
    inference(avatar_contradiction_clause,[],[f9164])).

fof(f9164,plain,
    ( $false
    | spl172_9
    | ~ spl172_28
    | ~ spl172_30
    | ~ spl172_43
    | ~ spl172_49 ),
    inference(subsumption_resolution,[],[f5967,f6281])).

fof(f6281,plain,
    ( ! [X0] : k6_tmap_1(sK0,sK1) != g1_pre_topc(X0,u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | spl172_9
    | ~ spl172_43
    | ~ spl172_49 ),
    inference(forward_demodulation,[],[f6275,f5415])).

fof(f5415,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ spl172_49 ),
    inference(avatar_component_clause,[],[f5413])).

fof(f5413,plain,
    ( spl172_49
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_49])])).

fof(f6275,plain,
    ( ! [X0] : g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) != g1_pre_topc(X0,u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | spl172_9
    | ~ spl172_43 ),
    inference(unit_resulting_resolution,[],[f5001,f5328,f4427])).

fof(f4427,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3680])).

fof(f3680,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1808])).

fof(f1808,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f5328,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl172_43 ),
    inference(avatar_component_clause,[],[f5326])).

fof(f5326,plain,
    ( spl172_43
  <=> m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_43])])).

fof(f5001,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl172_9 ),
    inference(avatar_component_clause,[],[f4999])).

fof(f4999,plain,
    ( spl172_9
  <=> k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_9])])).

fof(f5967,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ spl172_28
    | ~ spl172_30 ),
    inference(unit_resulting_resolution,[],[f5139,f5129,f4425])).

fof(f4425,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f3679])).

fof(f3679,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3678])).

fof(f3678,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f5129,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl172_28 ),
    inference(avatar_component_clause,[],[f5127])).

fof(f5127,plain,
    ( spl172_28
  <=> v1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_28])])).

fof(f5139,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl172_30 ),
    inference(avatar_component_clause,[],[f5137])).

fof(f5137,plain,
    ( spl172_30
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_30])])).

fof(f9163,plain,
    ( spl172_8
    | ~ spl172_28
    | ~ spl172_30
    | ~ spl172_43
    | ~ spl172_49 ),
    inference(avatar_contradiction_clause,[],[f9162])).

fof(f9162,plain,
    ( $false
    | spl172_8
    | ~ spl172_28
    | ~ spl172_30
    | ~ spl172_43
    | ~ spl172_49 ),
    inference(subsumption_resolution,[],[f5967,f6271])).

fof(f6271,plain,
    ( ! [X0] : k6_tmap_1(sK0,sK1) != g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),X0)
    | spl172_8
    | ~ spl172_43
    | ~ spl172_49 ),
    inference(forward_demodulation,[],[f6260,f5415])).

fof(f6260,plain,
    ( ! [X0] : g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) != g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),X0)
    | spl172_8
    | ~ spl172_43 ),
    inference(unit_resulting_resolution,[],[f4997,f5328,f4426])).

fof(f4426,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3680])).

fof(f4997,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1))
    | spl172_8 ),
    inference(avatar_component_clause,[],[f4995])).

fof(f4995,plain,
    ( spl172_8
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_8])])).

fof(f5416,plain,
    ( spl172_49
    | spl172_1
    | ~ spl172_2
    | ~ spl172_3
    | ~ spl172_5 ),
    inference(avatar_split_clause,[],[f5061,f4980,f4970,f4965,f4960,f5413])).

fof(f4960,plain,
    ( spl172_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_1])])).

fof(f4965,plain,
    ( spl172_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_2])])).

fof(f4970,plain,
    ( spl172_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_3])])).

fof(f4980,plain,
    ( spl172_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl172_5])])).

fof(f5061,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | spl172_1
    | ~ spl172_2
    | ~ spl172_3
    | ~ spl172_5 ),
    inference(unit_resulting_resolution,[],[f4962,f4967,f4972,f4982,f4131])).

fof(f4131,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3504])).

fof(f3504,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3503])).

fof(f3503,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3336])).

fof(f3336,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f4982,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl172_5 ),
    inference(avatar_component_clause,[],[f4980])).

fof(f4972,plain,
    ( l1_pre_topc(sK0)
    | ~ spl172_3 ),
    inference(avatar_component_clause,[],[f4970])).

fof(f4967,plain,
    ( v2_pre_topc(sK0)
    | ~ spl172_2 ),
    inference(avatar_component_clause,[],[f4965])).

fof(f4962,plain,
    ( ~ v2_struct_0(sK0)
    | spl172_1 ),
    inference(avatar_component_clause,[],[f4960])).

fof(f5329,plain,
    ( spl172_43
    | spl172_1
    | ~ spl172_2
    | ~ spl172_3
    | ~ spl172_5 ),
    inference(avatar_split_clause,[],[f5054,f4980,f4970,f4965,f4960,f5326])).

fof(f5054,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl172_1
    | ~ spl172_2
    | ~ spl172_3
    | ~ spl172_5 ),
    inference(unit_resulting_resolution,[],[f4962,f4967,f4972,f4982,f4120])).

fof(f4120,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3492])).

fof(f3492,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3491])).

fof(f3491,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3344])).

fof(f3344,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_tmap_1)).

fof(f5140,plain,
    ( spl172_30
    | spl172_1
    | ~ spl172_2
    | ~ spl172_3
    | ~ spl172_5 ),
    inference(avatar_split_clause,[],[f5041,f4980,f4970,f4965,f4960,f5137])).

fof(f5041,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl172_1
    | ~ spl172_2
    | ~ spl172_3
    | ~ spl172_5 ),
    inference(unit_resulting_resolution,[],[f4962,f4967,f4972,f4982,f4127])).

fof(f4127,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3500])).

fof(f3500,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3499])).

fof(f3499,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3345])).

fof(f3345,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f5130,plain,
    ( spl172_28
    | spl172_1
    | ~ spl172_2
    | ~ spl172_3
    | ~ spl172_5 ),
    inference(avatar_split_clause,[],[f5032,f4980,f4970,f4965,f4960,f5127])).

fof(f5032,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl172_1
    | ~ spl172_2
    | ~ spl172_3
    | ~ spl172_5 ),
    inference(unit_resulting_resolution,[],[f4962,f4967,f4972,f4982,f4125])).

fof(f4125,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3500])).

fof(f5002,plain,
    ( ~ spl172_8
    | ~ spl172_9 ),
    inference(avatar_split_clause,[],[f4044,f4999,f4995])).

fof(f4044,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))
    | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f3811])).

fof(f3811,plain,
    ( ( k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))
      | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f3479,f3810,f3809])).

fof(f3809,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1))
              | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k5_tmap_1(sK0,X1) != u1_pre_topc(k6_tmap_1(sK0,X1))
            | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3810,plain,
    ( ? [X1] :
        ( ( k5_tmap_1(sK0,X1) != u1_pre_topc(k6_tmap_1(sK0,X1))
          | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))
        | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f3479,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1))
            | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3478])).

fof(f3478,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1))
            | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3367])).

fof(f3367,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
              & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3366])).

fof(f3366,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f4983,plain,(
    spl172_5 ),
    inference(avatar_split_clause,[],[f4043,f4980])).

fof(f4043,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3811])).

fof(f4973,plain,(
    spl172_3 ),
    inference(avatar_split_clause,[],[f4042,f4970])).

fof(f4042,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3811])).

fof(f4968,plain,(
    spl172_2 ),
    inference(avatar_split_clause,[],[f4041,f4965])).

fof(f4041,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3811])).

fof(f4963,plain,(
    ~ spl172_1 ),
    inference(avatar_split_clause,[],[f4040,f4960])).

fof(f4040,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3811])).
%------------------------------------------------------------------------------
