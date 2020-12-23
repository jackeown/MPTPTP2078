%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1354+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:19 EST 2020

% Result     : Theorem 3.07s
% Output     : Refutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 247 expanded)
%              Number of leaves         :   13 (  78 expanded)
%              Depth                    :   12
%              Number of atoms          :  224 (1119 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5814,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2935,f2936,f5158,f5173,f5175,f5182,f5298,f5813])).

fof(f5813,plain,
    ( ~ spl24_118
    | spl24_119 ),
    inference(avatar_contradiction_clause,[],[f5812])).

fof(f5812,plain,
    ( $false
    | ~ spl24_118
    | spl24_119 ),
    inference(subsumption_resolution,[],[f5811,f4741])).

fof(f4741,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK2),sK3),u1_pre_topc(sK2))
    | spl24_119 ),
    inference(avatar_component_clause,[],[f4739])).

fof(f4739,plain,
    ( spl24_119
  <=> r1_tarski(k7_setfam_1(u1_struct_0(sK2),sK3),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_119])])).

fof(f5811,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0(sK2),sK3),u1_pre_topc(sK2))
    | ~ spl24_118 ),
    inference(subsumption_resolution,[],[f5808,f3005])).

fof(f3005,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f2684,f2795])).

fof(f2795,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2524])).

fof(f2524,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f565])).

fof(f565,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f2684,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f2603])).

fof(f2603,plain,
    ( ( ~ r1_tarski(sK3,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ v2_tops_2(sK3,sK2) )
    & ( r1_tarski(sK3,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | v2_tops_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f2600,f2602,f2601])).

fof(f2601,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ v2_tops_2(X1,X0) )
            & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
              | v2_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)))
            | ~ v2_tops_2(X1,sK2) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)))
            | v2_tops_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2602,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)))
          | ~ v2_tops_2(X1,sK2) )
        & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)))
          | v2_tops_2(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ( ~ r1_tarski(sK3,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | ~ v2_tops_2(sK3,sK2) )
      & ( r1_tarski(sK3,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | v2_tops_2(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f2600,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ v2_tops_2(X1,X0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2599])).

fof(f2599,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ v2_tops_2(X1,X0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2443])).

fof(f2443,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_2(X1,X0)
          <~> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2434])).

fof(f2434,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
            <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f2433])).

fof(f2433,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_2)).

fof(f5808,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r1_tarski(k7_setfam_1(u1_struct_0(sK2),sK3),u1_pre_topc(sK2))
    | ~ spl24_118 ),
    inference(resolution,[],[f2942,f4737])).

fof(f4737,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK2),sK3),sK2)
    | ~ spl24_118 ),
    inference(avatar_component_clause,[],[f4735])).

fof(f4735,plain,
    ( spl24_118
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK2),sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_118])])).

fof(f2942,plain,(
    ! [X5] :
      ( ~ v1_tops_2(X5,sK2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | r1_tarski(X5,u1_pre_topc(sK2)) ) ),
    inference(resolution,[],[f2683,f2822])).

fof(f2822,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r1_tarski(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f2645])).

fof(f2645,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2547])).

fof(f2547,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2432])).

fof(f2432,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(f2683,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f2603])).

fof(f5298,plain,
    ( spl24_118
    | ~ spl24_119 ),
    inference(avatar_split_clause,[],[f5258,f4739,f4735])).

fof(f5258,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK2),sK3),u1_pre_topc(sK2))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(resolution,[],[f3005,f2943])).

fof(f2943,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | ~ r1_tarski(X6,u1_pre_topc(sK2))
      | v1_tops_2(X6,sK2) ) ),
    inference(resolution,[],[f2683,f2823])).

fof(f2823,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f2645])).

fof(f5182,plain,
    ( spl24_2
    | ~ spl24_119 ),
    inference(avatar_split_clause,[],[f5119,f4739,f2932])).

fof(f2932,plain,
    ( spl24_2
  <=> r1_tarski(sK3,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_2])])).

fof(f5119,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK2),sK3),u1_pre_topc(sK2))
    | r1_tarski(sK3,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f2994,f2959])).

fof(f2959,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f2683,f2863])).

fof(f2863,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f2561])).

fof(f2561,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f2994,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | ~ r1_tarski(k7_setfam_1(u1_struct_0(sK2),sK3),X0)
      | r1_tarski(sK3,k7_setfam_1(u1_struct_0(sK2),X0)) ) ),
    inference(resolution,[],[f2684,f2775])).

fof(f2775,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r1_tarski(k7_setfam_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r1_tarski(X1,k7_setfam_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f2629])).

fof(f2629,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
              | ~ r1_tarski(X1,k7_setfam_1(X0,X2)) )
            & ( r1_tarski(X1,k7_setfam_1(X0,X2))
              | ~ r1_tarski(k7_setfam_1(X0,X1),X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f2503])).

fof(f2503,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f620])).

fof(f620,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).

fof(f5175,plain,
    ( ~ spl24_118
    | spl24_1 ),
    inference(avatar_split_clause,[],[f5174,f2928,f4735])).

fof(f2928,plain,
    ( spl24_1
  <=> v2_tops_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_1])])).

fof(f5174,plain,
    ( v2_tops_2(sK3,sK2)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(subsumption_resolution,[],[f4894,f3005])).

fof(f4894,plain,
    ( v2_tops_2(sK3,sK2)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(superposition,[],[f2937,f3006])).

fof(f3006,plain,(
    sK3 = k7_setfam_1(u1_struct_0(sK2),k7_setfam_1(u1_struct_0(sK2),sK3)) ),
    inference(resolution,[],[f2684,f2796])).

fof(f2796,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2525])).

fof(f2525,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f574])).

fof(f574,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f2937,plain,(
    ! [X0] :
      ( v2_tops_2(k7_setfam_1(u1_struct_0(sK2),X0),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | ~ v1_tops_2(X0,sK2) ) ),
    inference(resolution,[],[f2683,f2797])).

fof(f2797,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f2636])).

fof(f2636,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2526])).

fof(f2526,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2366])).

fof(f2366,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tops_2)).

fof(f5173,plain,
    ( spl24_118
    | ~ spl24_1 ),
    inference(avatar_split_clause,[],[f5172,f2928,f4735])).

fof(f5172,plain,
    ( ~ v2_tops_2(sK3,sK2)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(subsumption_resolution,[],[f4899,f3005])).

fof(f4899,plain,
    ( ~ v2_tops_2(sK3,sK2)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK2),sK3),sK2) ),
    inference(superposition,[],[f2938,f3006])).

fof(f2938,plain,(
    ! [X1] :
      ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK2),X1),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | v1_tops_2(X1,sK2) ) ),
    inference(resolution,[],[f2683,f2798])).

fof(f2798,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f2636])).

fof(f5158,plain,
    ( ~ spl24_2
    | spl24_119 ),
    inference(avatar_contradiction_clause,[],[f5157])).

fof(f5157,plain,
    ( $false
    | ~ spl24_2
    | spl24_119 ),
    inference(subsumption_resolution,[],[f5156,f4741])).

fof(f5156,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0(sK2),sK3),u1_pre_topc(sK2))
    | ~ spl24_2 ),
    inference(subsumption_resolution,[],[f5154,f2959])).

fof(f5154,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r1_tarski(k7_setfam_1(u1_struct_0(sK2),sK3),u1_pre_topc(sK2))
    | ~ spl24_2 ),
    inference(resolution,[],[f2995,f2933])).

fof(f2933,plain,
    ( r1_tarski(sK3,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl24_2 ),
    inference(avatar_component_clause,[],[f2932])).

fof(f2995,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK3,k7_setfam_1(u1_struct_0(sK2),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | r1_tarski(k7_setfam_1(u1_struct_0(sK2),sK3),X1) ) ),
    inference(resolution,[],[f2684,f2776])).

fof(f2776,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r1_tarski(X1,k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r1_tarski(k7_setfam_1(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f2629])).

fof(f2936,plain,
    ( spl24_1
    | spl24_2 ),
    inference(avatar_split_clause,[],[f2685,f2932,f2928])).

fof(f2685,plain,
    ( r1_tarski(sK3,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v2_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f2603])).

fof(f2935,plain,
    ( ~ spl24_1
    | ~ spl24_2 ),
    inference(avatar_split_clause,[],[f2686,f2932,f2928])).

fof(f2686,plain,
    ( ~ r1_tarski(sK3,k7_setfam_1(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f2603])).
%------------------------------------------------------------------------------
