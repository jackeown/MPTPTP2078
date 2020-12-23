%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1262+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:14 EST 2020

% Result     : Theorem 3.01s
% Output     : Refutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 182 expanded)
%              Number of leaves         :   23 (  82 expanded)
%              Depth                    :    8
%              Number of atoms          :  284 ( 696 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3610,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2514,f2519,f2524,f2529,f2539,f2549,f2692,f2705,f3217,f3281,f3373,f3584,f3609])).

fof(f3609,plain,
    ( ~ spl38_61
    | spl38_67
    | ~ spl38_75 ),
    inference(avatar_contradiction_clause,[],[f3608])).

fof(f3608,plain,
    ( $false
    | ~ spl38_61
    | spl38_67
    | ~ spl38_75 ),
    inference(subsumption_resolution,[],[f3599,f3288])).

fof(f3288,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
    | ~ spl38_61 ),
    inference(unit_resulting_resolution,[],[f3280,f2355])).

fof(f2355,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2272])).

fof(f2272,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f3280,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl38_61 ),
    inference(avatar_component_clause,[],[f3278])).

fof(f3278,plain,
    ( spl38_61
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_61])])).

fof(f3599,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
    | spl38_67
    | ~ spl38_75 ),
    inference(unit_resulting_resolution,[],[f3372,f3583,f2366])).

fof(f2366,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2282])).

fof(f2282,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2281])).

fof(f2281,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3583,plain,
    ( r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK2))
    | ~ spl38_75 ),
    inference(avatar_component_clause,[],[f3581])).

fof(f3581,plain,
    ( spl38_75
  <=> r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_75])])).

fof(f3372,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK2)
    | spl38_67 ),
    inference(avatar_component_clause,[],[f3370])).

fof(f3370,plain,
    ( spl38_67
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_67])])).

fof(f3584,plain,
    ( spl38_75
    | ~ spl38_1
    | ~ spl38_3
    | ~ spl38_6
    | ~ spl38_8
    | ~ spl38_24
    | ~ spl38_60 ),
    inference(avatar_split_clause,[],[f3303,f3214,f2689,f2546,f2536,f2521,f2511,f3581])).

fof(f2511,plain,
    ( spl38_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_1])])).

fof(f2521,plain,
    ( spl38_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_3])])).

fof(f2536,plain,
    ( spl38_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_6])])).

fof(f2546,plain,
    ( spl38_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_8])])).

fof(f2689,plain,
    ( spl38_24
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_24])])).

fof(f3214,plain,
    ( spl38_60
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_60])])).

fof(f3303,plain,
    ( r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK2))
    | ~ spl38_1
    | ~ spl38_3
    | ~ spl38_6
    | ~ spl38_8
    | ~ spl38_24
    | ~ spl38_60 ),
    inference(backward_demodulation,[],[f2867,f3296])).

fof(f3296,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl38_60 ),
    inference(unit_resulting_resolution,[],[f3216,f2404])).

fof(f2404,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2196])).

fof(f2196,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3216,plain,
    ( l1_struct_0(sK0)
    | ~ spl38_60 ),
    inference(avatar_component_clause,[],[f3214])).

fof(f2867,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK2))
    | ~ spl38_1
    | ~ spl38_3
    | ~ spl38_6
    | ~ spl38_8
    | ~ spl38_24 ),
    inference(forward_demodulation,[],[f2854,f2691])).

fof(f2691,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl38_24 ),
    inference(avatar_component_clause,[],[f2689])).

fof(f2854,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ spl38_1
    | ~ spl38_3
    | ~ spl38_6
    | ~ spl38_8 ),
    inference(unit_resulting_resolution,[],[f2513,f2523,f2538,f2548,f2408])).

fof(f2408,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f2203])).

fof(f2203,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2202])).

fof(f2202,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1840])).

fof(f1840,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f2548,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl38_8 ),
    inference(avatar_component_clause,[],[f2546])).

fof(f2538,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl38_6 ),
    inference(avatar_component_clause,[],[f2536])).

fof(f2523,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl38_3 ),
    inference(avatar_component_clause,[],[f2521])).

fof(f2513,plain,
    ( l1_pre_topc(sK0)
    | ~ spl38_1 ),
    inference(avatar_component_clause,[],[f2511])).

fof(f3373,plain,
    ( ~ spl38_67
    | spl38_26
    | ~ spl38_60 ),
    inference(avatar_split_clause,[],[f3300,f3214,f2702,f3370])).

fof(f2702,plain,
    ( spl38_26
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_26])])).

fof(f3300,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK2)
    | spl38_26
    | ~ spl38_60 ),
    inference(backward_demodulation,[],[f2704,f3296])).

fof(f2704,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK2)
    | spl38_26 ),
    inference(avatar_component_clause,[],[f2702])).

fof(f3281,plain,
    ( spl38_61
    | ~ spl38_1
    | ~ spl38_8 ),
    inference(avatar_split_clause,[],[f2827,f2546,f2511,f3278])).

fof(f2827,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl38_1
    | ~ spl38_8 ),
    inference(unit_resulting_resolution,[],[f2513,f2548,f2407])).

fof(f2407,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f2201])).

fof(f2201,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2200])).

fof(f2200,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1780])).

fof(f1780,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f3217,plain,
    ( spl38_60
    | ~ spl38_1 ),
    inference(avatar_split_clause,[],[f3211,f2511,f3214])).

fof(f3211,plain,
    ( l1_struct_0(sK0)
    | ~ spl38_1 ),
    inference(unit_resulting_resolution,[],[f2513,f2448])).

fof(f2448,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2232])).

fof(f2232,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2705,plain,
    ( ~ spl38_26
    | ~ spl38_1
    | spl38_4
    | ~ spl38_8 ),
    inference(avatar_split_clause,[],[f2613,f2546,f2526,f2511,f2702])).

fof(f2526,plain,
    ( spl38_4
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_4])])).

fof(f2613,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK2)
    | ~ spl38_1
    | spl38_4
    | ~ spl38_8 ),
    inference(unit_resulting_resolution,[],[f2513,f2528,f2548,f2376])).

fof(f2376,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2289])).

fof(f2289,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2170])).

fof(f2170,plain,(
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

fof(f2528,plain,
    ( ~ v1_tops_1(sK2,sK0)
    | spl38_4 ),
    inference(avatar_component_clause,[],[f2526])).

fof(f2692,plain,
    ( spl38_24
    | ~ spl38_1
    | ~ spl38_2
    | ~ spl38_6 ),
    inference(avatar_split_clause,[],[f2612,f2536,f2516,f2511,f2689])).

fof(f2516,plain,
    ( spl38_2
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl38_2])])).

fof(f2612,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl38_1
    | ~ spl38_2
    | ~ spl38_6 ),
    inference(unit_resulting_resolution,[],[f2513,f2518,f2538,f2375])).

fof(f2375,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2289])).

fof(f2518,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl38_2 ),
    inference(avatar_component_clause,[],[f2516])).

fof(f2549,plain,(
    spl38_8 ),
    inference(avatar_split_clause,[],[f2349,f2546])).

fof(f2349,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2271])).

fof(f2271,plain,
    ( ~ v1_tops_1(sK2,sK0)
    & r1_tarski(sK1,sK2)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2159,f2270,f2269,f2268])).

fof(f2268,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(X2,X0)
                & r1_tarski(X1,X2)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(X2,sK0)
              & r1_tarski(X1,X2)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2269,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_1(X2,sK0)
            & r1_tarski(X1,X2)
            & v1_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v1_tops_1(X2,sK0)
          & r1_tarski(sK1,X2)
          & v1_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2270,plain,
    ( ? [X2] :
        ( ~ v1_tops_1(X2,sK0)
        & r1_tarski(sK1,X2)
        & v1_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(sK2,sK0)
      & r1_tarski(sK1,sK2)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2159,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(X2,X0)
              & r1_tarski(X1,X2)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2158])).

fof(f2158,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(X2,X0)
              & r1_tarski(X1,X2)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2157])).

fof(f2157,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X1,X2)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f2156])).

fof(f2156,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

fof(f2539,plain,(
    spl38_6 ),
    inference(avatar_split_clause,[],[f2348,f2536])).

fof(f2348,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2271])).

fof(f2529,plain,(
    ~ spl38_4 ),
    inference(avatar_split_clause,[],[f2352,f2526])).

fof(f2352,plain,(
    ~ v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f2271])).

fof(f2524,plain,(
    spl38_3 ),
    inference(avatar_split_clause,[],[f2351,f2521])).

fof(f2351,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f2271])).

fof(f2519,plain,(
    spl38_2 ),
    inference(avatar_split_clause,[],[f2350,f2516])).

fof(f2350,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2271])).

fof(f2514,plain,(
    spl38_1 ),
    inference(avatar_split_clause,[],[f2347,f2511])).

fof(f2347,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2271])).
%------------------------------------------------------------------------------
