%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1265+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:14 EST 2020

% Result     : Theorem 2.58s
% Output     : Refutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 165 expanded)
%              Number of leaves         :   18 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  259 ( 883 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3477,f3482,f3487,f3492,f3497,f3507,f3517,f3532,f3578,f4418])).

fof(f4418,plain,
    ( ~ spl95_1
    | ~ spl95_2
    | ~ spl95_3
    | ~ spl95_4
    | ~ spl95_5
    | ~ spl95_7
    | ~ spl95_9
    | spl95_17 ),
    inference(avatar_contradiction_clause,[],[f4417])).

fof(f4417,plain,
    ( $false
    | ~ spl95_1
    | ~ spl95_2
    | ~ spl95_3
    | ~ spl95_4
    | ~ spl95_5
    | ~ spl95_7
    | ~ spl95_9
    | spl95_17 ),
    inference(subsumption_resolution,[],[f4363,f3677])).

fof(f3677,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ spl95_1
    | ~ spl95_2
    | ~ spl95_3
    | ~ spl95_4
    | ~ spl95_5
    | ~ spl95_7
    | ~ spl95_9 ),
    inference(forward_demodulation,[],[f3676,f3591])).

fof(f3591,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)
    | ~ spl95_2
    | ~ spl95_4
    | ~ spl95_9 ),
    inference(unit_resulting_resolution,[],[f3481,f3491,f3516,f2819])).

fof(f2819,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2582])).

fof(f2582,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2203])).

fof(f2203,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2089])).

fof(f2089,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f3516,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl95_9 ),
    inference(avatar_component_clause,[],[f3514])).

fof(f3514,plain,
    ( spl95_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl95_9])])).

fof(f3491,plain,
    ( v1_tops_1(sK2,sK0)
    | ~ spl95_4 ),
    inference(avatar_component_clause,[],[f3489])).

fof(f3489,plain,
    ( spl95_4
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl95_4])])).

fof(f3481,plain,
    ( l1_pre_topc(sK0)
    | ~ spl95_2 ),
    inference(avatar_component_clause,[],[f3479])).

fof(f3479,plain,
    ( spl95_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl95_2])])).

fof(f3676,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ spl95_1
    | ~ spl95_2
    | ~ spl95_3
    | ~ spl95_5
    | ~ spl95_7
    | ~ spl95_9 ),
    inference(forward_demodulation,[],[f3673,f3566])).

fof(f3566,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl95_7 ),
    inference(unit_resulting_resolution,[],[f3506,f2781])).

fof(f2781,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2171])).

fof(f2171,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f3506,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl95_7 ),
    inference(avatar_component_clause,[],[f3504])).

fof(f3504,plain,
    ( spl95_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl95_7])])).

fof(f3673,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    | ~ spl95_1
    | ~ spl95_2
    | ~ spl95_3
    | ~ spl95_5
    | ~ spl95_7
    | ~ spl95_9 ),
    inference(unit_resulting_resolution,[],[f3476,f3481,f3496,f3486,f3506,f3516,f2815])).

fof(f2815,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ),
    inference(cnf_transformation,[],[f2199])).

fof(f2199,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2198])).

fof(f2198,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2160])).

fof(f2160,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

fof(f3486,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl95_3 ),
    inference(avatar_component_clause,[],[f3484])).

fof(f3484,plain,
    ( spl95_3
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl95_3])])).

fof(f3496,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl95_5 ),
    inference(avatar_component_clause,[],[f3494])).

fof(f3494,plain,
    ( spl95_5
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl95_5])])).

fof(f3476,plain,
    ( v2_pre_topc(sK0)
    | ~ spl95_1 ),
    inference(avatar_component_clause,[],[f3474])).

fof(f3474,plain,
    ( spl95_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl95_1])])).

fof(f4363,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ spl95_2
    | ~ spl95_7
    | spl95_17 ),
    inference(unit_resulting_resolution,[],[f3481,f3577,f3573,f2820])).

fof(f2820,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2582])).

fof(f3573,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl95_7 ),
    inference(backward_demodulation,[],[f3563,f3566])).

fof(f3563,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl95_7 ),
    inference(unit_resulting_resolution,[],[f3506,f2782])).

fof(f2782,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2172])).

fof(f2172,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f472])).

fof(f472,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f3577,plain,
    ( ~ v1_tops_1(k3_xboole_0(sK2,sK1),sK0)
    | spl95_17 ),
    inference(avatar_component_clause,[],[f3575])).

fof(f3575,plain,
    ( spl95_17
  <=> v1_tops_1(k3_xboole_0(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl95_17])])).

fof(f3578,plain,
    ( ~ spl95_17
    | ~ spl95_9
    | spl95_12 ),
    inference(avatar_split_clause,[],[f3572,f3529,f3514,f3575])).

fof(f3529,plain,
    ( spl95_12
  <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl95_12])])).

fof(f3572,plain,
    ( ~ v1_tops_1(k3_xboole_0(sK2,sK1),sK0)
    | ~ spl95_9
    | spl95_12 ),
    inference(forward_demodulation,[],[f3571,f2863])).

fof(f2863,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f3571,plain,
    ( ~ v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl95_9
    | spl95_12 ),
    inference(backward_demodulation,[],[f3531,f3567])).

fof(f3567,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl95_9 ),
    inference(unit_resulting_resolution,[],[f3516,f2781])).

fof(f3531,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl95_12 ),
    inference(avatar_component_clause,[],[f3529])).

fof(f3532,plain,(
    ~ spl95_12 ),
    inference(avatar_split_clause,[],[f2779,f3529])).

fof(f2779,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f2561])).

fof(f2561,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2169,f2560,f2559,f2558])).

fof(f2558,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v1_tops_1(X2,X0)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v1_tops_1(X2,sK0)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2559,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v3_pre_topc(X2,sK0)
            & v1_tops_1(X2,sK0)
            & v1_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v3_pre_topc(X2,sK0)
          & v1_tops_1(X2,sK0)
          & v1_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2560,plain,
    ( ? [X2] :
        ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v3_pre_topc(X2,sK0)
        & v1_tops_1(X2,sK0)
        & v1_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v3_pre_topc(sK2,sK0)
      & v1_tops_1(sK2,sK0)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2169,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2168])).

fof(f2168,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2162])).

fof(f2162,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v1_tops_1(X2,X0)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f2161])).

fof(f2161,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v1_tops_1(X2,X0)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).

fof(f3517,plain,(
    spl95_9 ),
    inference(avatar_split_clause,[],[f2775,f3514])).

fof(f2775,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2561])).

fof(f3507,plain,(
    spl95_7 ),
    inference(avatar_split_clause,[],[f2774,f3504])).

fof(f2774,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2561])).

fof(f3497,plain,(
    spl95_5 ),
    inference(avatar_split_clause,[],[f2778,f3494])).

fof(f2778,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f2561])).

fof(f3492,plain,(
    spl95_4 ),
    inference(avatar_split_clause,[],[f2777,f3489])).

fof(f2777,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f2561])).

fof(f3487,plain,(
    spl95_3 ),
    inference(avatar_split_clause,[],[f2776,f3484])).

fof(f2776,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2561])).

fof(f3482,plain,(
    spl95_2 ),
    inference(avatar_split_clause,[],[f2773,f3479])).

fof(f2773,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2561])).

fof(f3477,plain,(
    spl95_1 ),
    inference(avatar_split_clause,[],[f2772,f3474])).

fof(f2772,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2561])).
%------------------------------------------------------------------------------
