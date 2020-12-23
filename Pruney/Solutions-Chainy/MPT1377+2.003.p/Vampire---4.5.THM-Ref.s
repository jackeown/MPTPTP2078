%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  181 (3213 expanded)
%              Number of leaves         :   21 ( 803 expanded)
%              Depth                    :   30
%              Number of atoms          :  705 (18312 expanded)
%              Number of equality atoms :   72 ( 776 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f671,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f89,f92,f125,f208,f244,f332,f469,f477,f595,f612,f616,f633,f670])).

fof(f670,plain,
    ( ~ spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f669])).

fof(f669,plain,
    ( $false
    | ~ spl2_2
    | spl2_4 ),
    inference(subsumption_resolution,[],[f78,f639])).

fof(f639,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_4 ),
    inference(forward_demodulation,[],[f87,f181])).

fof(f181,plain,(
    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(trivial_inequality_removal,[],[f180])).

fof(f180,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(superposition,[],[f111,f110])).

fof(f110,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f109,f95])).

fof(f95,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f62,f93])).

fof(f93,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_compts_1(sK1,sK0) ) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_compts_1(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_compts_1(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v2_compts_1(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_compts_1(X1,sK0) ) ) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v2_compts_1(X1,sK0) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & v2_compts_1(X1,sK0) ) ) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_compts_1(sK1,sK0) )
      & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
        | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v2_compts_1(sK1,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_compts_1)).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f109,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f94,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f94,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f61,f93])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f111,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f63,f93])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f87,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f633,plain,
    ( ~ spl2_2
    | ~ spl2_6
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_6
    | spl2_11 ),
    inference(global_subsumption,[],[f627,f243])).

fof(f243,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl2_11
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f627,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f78,f124])).

fof(f124,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl2_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f616,plain,
    ( spl2_3
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | spl2_3
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(global_subsumption,[],[f219,f242,f235,f613])).

fof(f613,plain,
    ( ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f83,f124])).

fof(f83,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_3
  <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f235,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl2_9
  <=> v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f242,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f241])).

fof(f219,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f199,f95])).

fof(f199,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(superposition,[],[f67,f181])).

fof(f67,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | v2_compts_1(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v1_compts_1(k1_pre_topc(X0,X1))
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

fof(f612,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | spl2_9 ),
    inference(avatar_contradiction_clause,[],[f611])).

fof(f611,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | spl2_9 ),
    inference(subsumption_resolution,[],[f610,f579])).

fof(f579,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f578,f124])).

fof(f578,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f120,f228])).

fof(f228,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f227,f42])).

fof(f227,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f186,f191])).

fof(f191,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(superposition,[],[f86,f181])).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f186,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f157,f155])).

fof(f155,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f151,f42])).

fof(f151,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f106,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f106,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f105,f95])).

fof(f105,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f66,f86])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f156,f104])).

fof(f104,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f103,f95])).

fof(f103,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f65,f86])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
        | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_4 ),
    inference(superposition,[],[f70,f154])).

fof(f154,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f153,f95])).

fof(f153,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f152,f86])).

% (5222)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f152,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f150,f104])).

fof(f150,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f106,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | k1_pre_topc(X0,k2_struct_0(X2)) = X2
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_pre_topc(X0,X1) = X2
      | k2_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f120,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl2_5
  <=> v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f610,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_6
    | spl2_9 ),
    inference(forward_demodulation,[],[f234,f489])).

fof(f489,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f228,f124])).

fof(f234,plain,
    ( ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f233])).

fof(f595,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f594])).

fof(f594,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f593,f42])).

fof(f593,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f592,f478])).

fof(f478,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | spl2_1
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f75,f124])).

fof(f75,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_1
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f592,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f581,f577])).

fof(f577,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f235,f489])).

fof(f581,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | v2_compts_1(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(resolution,[],[f501,f67])).

fof(f501,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f480,f181])).

fof(f480,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f86,f124])).

fof(f477,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | spl2_10 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_6
    | spl2_10 ),
    inference(subsumption_resolution,[],[f475,f239])).

fof(f239,plain,
    ( ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl2_10
  <=> v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f475,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f82,f124])).

fof(f82,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f469,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | spl2_5 ),
    inference(subsumption_resolution,[],[f467,f42])).

fof(f467,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | spl2_5 ),
    inference(subsumption_resolution,[],[f466,f381])).

fof(f381,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_4
    | spl2_5 ),
    inference(superposition,[],[f346,f349])).

fof(f349,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_1
    | ~ spl2_4
    | spl2_5 ),
    inference(subsumption_resolution,[],[f348,f42])).

fof(f348,plain,
    ( k1_xboole_0 = sK1
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | spl2_5 ),
    inference(subsumption_resolution,[],[f347,f346])).

fof(f347,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f340,f41])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f340,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_pre_topc(sK0)
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f274,f74])).

fof(f74,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f274,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | k1_xboole_0 = sK1
    | ~ v2_pre_topc(sK0)
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f191,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | v1_compts_1(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f346,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl2_4
    | spl2_5 ),
    inference(forward_demodulation,[],[f119,f228])).

fof(f119,plain,
    ( ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f466,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | spl2_5 ),
    inference(subsumption_resolution,[],[f454,f350])).

fof(f350,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl2_1
    | ~ spl2_4
    | spl2_5 ),
    inference(superposition,[],[f74,f349])).

fof(f454,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | spl2_5 ),
    inference(resolution,[],[f360,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(k1_xboole_0,X0)
      | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f360,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_4
    | spl2_5 ),
    inference(superposition,[],[f191,f349])).

fof(f332,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(global_subsumption,[],[f47,f86,f191,f318,f322])).

fof(f322,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(subsumption_resolution,[],[f321,f95])).

fof(f321,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(subsumption_resolution,[],[f320,f98])).

fof(f98,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f97,f42])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f60,f41])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f320,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(subsumption_resolution,[],[f319,f123])).

fof(f123,plain,
    ( k1_xboole_0 != sK1
    | spl2_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f319,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f126,f120])).

fof(f126,plain,
    ( ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | k1_xboole_0 = sK1
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f54,f86])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_compts_1(k1_pre_topc(X0,X1))
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | v2_compts_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f318,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(subsumption_resolution,[],[f317,f42])).

fof(f317,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(subsumption_resolution,[],[f279,f304])).

fof(f304,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f120,f228])).

fof(f279,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | spl2_6 ),
    inference(subsumption_resolution,[],[f278,f41])).

fof(f278,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | spl2_6 ),
    inference(subsumption_resolution,[],[f273,f123])).

fof(f273,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | k1_xboole_0 = sK1
    | ~ v2_pre_topc(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f191,f54])).

fof(f47,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f244,plain,
    ( spl2_9
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f220,f241,f237,f233])).

fof(f220,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f200,f95])).

fof(f200,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(superposition,[],[f68,f181])).

fof(f208,plain,
    ( spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f191,f79])).

fof(f79,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f125,plain,
    ( spl2_5
    | spl2_6
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f116,f85,f81,f122,f118])).

fof(f116,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f115,f95])).

fof(f115,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f114,f98])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f113,f82])).

fof(f113,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | k1_xboole_0 = sK1
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f53,f86])).

fof(f92,plain,
    ( spl2_1
    | spl2_3 ),
    inference(avatar_split_clause,[],[f43,f81,f73])).

fof(f43,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,
    ( spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f46,f85,f77])).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f47,f85,f81,f77,f73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (5221)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.47  % (5221)Refutation not found, incomplete strategy% (5221)------------------------------
% 0.21/0.47  % (5221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5236)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.48  % (5221)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (5221)Memory used [KB]: 10618
% 0.21/0.48  % (5221)Time elapsed: 0.081 s
% 0.21/0.48  % (5221)------------------------------
% 0.21/0.48  % (5221)------------------------------
% 0.21/0.49  % (5218)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (5225)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (5224)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.49  % (5241)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.50  % (5220)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (5226)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (5223)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (5229)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (5233)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (5232)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.50  % (5237)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (5220)Refutation not found, incomplete strategy% (5220)------------------------------
% 0.21/0.50  % (5220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5220)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5220)Memory used [KB]: 6268
% 0.21/0.50  % (5220)Time elapsed: 0.098 s
% 0.21/0.50  % (5220)------------------------------
% 0.21/0.50  % (5220)------------------------------
% 0.21/0.50  % (5217)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (5216)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (5240)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.50  % (5219)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (5235)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (5216)Refutation not found, incomplete strategy% (5216)------------------------------
% 0.21/0.50  % (5216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5216)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5216)Memory used [KB]: 10618
% 0.21/0.50  % (5216)Time elapsed: 0.095 s
% 0.21/0.50  % (5216)------------------------------
% 0.21/0.50  % (5216)------------------------------
% 0.21/0.51  % (5239)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (5215)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (5238)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (5225)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f671,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f88,f89,f92,f125,f208,f244,f332,f469,f477,f595,f612,f616,f633,f670])).
% 0.21/0.51  fof(f670,plain,(
% 0.21/0.51    ~spl2_2 | spl2_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f669])).
% 0.21/0.51  fof(f669,plain,(
% 0.21/0.51    $false | (~spl2_2 | spl2_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f78,f639])).
% 0.21/0.51  fof(f639,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_4),
% 0.21/0.51    inference(forward_demodulation,[],[f87,f181])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f180])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.51    inference(superposition,[],[f111,f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f109,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.51    inference(resolution,[],[f62,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    inference(resolution,[],[f48,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_compts_1)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.51    inference(resolution,[],[f94,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.51    inference(resolution,[],[f61,f93])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = X0) )),
% 0.21/0.51    inference(resolution,[],[f63,f93])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f633,plain,(
% 0.21/0.51    ~spl2_2 | ~spl2_6 | spl2_11),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f632])).
% 0.21/0.52  fof(f632,plain,(
% 0.21/0.52    $false | (~spl2_2 | ~spl2_6 | spl2_11)),
% 0.21/0.52    inference(global_subsumption,[],[f627,f243])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f241])).
% 0.21/0.52  fof(f241,plain,(
% 0.21/0.52    spl2_11 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.52  fof(f627,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_6)),
% 0.21/0.52    inference(forward_demodulation,[],[f78,f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl2_6 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.52  fof(f616,plain,(
% 0.21/0.52    spl2_3 | ~spl2_6 | ~spl2_9 | ~spl2_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f615])).
% 0.21/0.52  fof(f615,plain,(
% 0.21/0.52    $false | (spl2_3 | ~spl2_6 | ~spl2_9 | ~spl2_11)),
% 0.21/0.52    inference(global_subsumption,[],[f219,f242,f235,f613])).
% 0.21/0.52  fof(f613,plain,(
% 0.21/0.52    ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl2_3 | ~spl2_6)),
% 0.21/0.52    inference(forward_demodulation,[],[f83,f124])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl2_3 <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | ~spl2_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f233])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    spl2_9 <=> v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f241])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f199,f95])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    inference(superposition,[],[f67,f181])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | v2_compts_1(k1_xboole_0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1)) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & (((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).
% 0.21/0.52  fof(f612,plain,(
% 0.21/0.52    ~spl2_4 | ~spl2_5 | ~spl2_6 | spl2_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f611])).
% 0.21/0.52  fof(f611,plain,(
% 0.21/0.52    $false | (~spl2_4 | ~spl2_5 | ~spl2_6 | spl2_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f610,f579])).
% 0.21/0.52  fof(f579,plain,(
% 0.21/0.52    v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | (~spl2_4 | ~spl2_5 | ~spl2_6)),
% 0.21/0.52    inference(forward_demodulation,[],[f578,f124])).
% 0.21/0.52  fof(f578,plain,(
% 0.21/0.52    v1_compts_1(k1_pre_topc(sK0,sK1)) | (~spl2_4 | ~spl2_5)),
% 0.21/0.52    inference(forward_demodulation,[],[f120,f228])).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) | ~spl2_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f227,f42])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f186,f191])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.21/0.52    inference(superposition,[],[f86,f181])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f85])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f157,f155])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~spl2_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f151,f42])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f106,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f105,f95])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f66,f86])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0)) ) | ~spl2_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f156,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f103,f95])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f65,f86])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0)) ) | ~spl2_4),
% 0.21/0.52    inference(superposition,[],[f70,f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f153,f95])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f152,f86])).
% 0.21/0.52  % (5222)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f150,f104])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f106,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0] : (~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | k1_pre_topc(X0,k2_struct_0(X2)) = X2 | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl2_5 <=> v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f610,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | (~spl2_4 | ~spl2_6 | spl2_9)),
% 0.21/0.52    inference(forward_demodulation,[],[f234,f489])).
% 0.21/0.52  fof(f489,plain,(
% 0.21/0.52    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0) | (~spl2_4 | ~spl2_6)),
% 0.21/0.52    inference(superposition,[],[f228,f124])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | spl2_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f233])).
% 0.21/0.52  fof(f595,plain,(
% 0.21/0.52    spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f594])).
% 0.21/0.52  fof(f594,plain,(
% 0.21/0.52    $false | (spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f593,f42])).
% 0.21/0.52  fof(f593,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f592,f478])).
% 0.21/0.52  fof(f478,plain,(
% 0.21/0.52    ~v2_compts_1(k1_xboole_0,sK0) | (spl2_1 | ~spl2_6)),
% 0.21/0.52    inference(forward_demodulation,[],[f75,f124])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ~v2_compts_1(sK1,sK0) | spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl2_1 <=> v2_compts_1(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f592,plain,(
% 0.21/0.52    v2_compts_1(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_6 | ~spl2_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f581,f577])).
% 0.21/0.52  fof(f577,plain,(
% 0.21/0.52    v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | (~spl2_4 | ~spl2_6 | ~spl2_9)),
% 0.21/0.52    inference(forward_demodulation,[],[f235,f489])).
% 0.21/0.52  fof(f581,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | v2_compts_1(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_6)),
% 0.21/0.52    inference(resolution,[],[f501,f67])).
% 0.21/0.52  fof(f501,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | ~spl2_6)),
% 0.21/0.52    inference(forward_demodulation,[],[f480,f181])).
% 0.21/0.52  fof(f480,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | (~spl2_4 | ~spl2_6)),
% 0.21/0.52    inference(superposition,[],[f86,f124])).
% 0.21/0.52  fof(f477,plain,(
% 0.21/0.52    ~spl2_3 | ~spl2_6 | spl2_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f476])).
% 0.21/0.52  fof(f476,plain,(
% 0.21/0.52    $false | (~spl2_3 | ~spl2_6 | spl2_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f475,f239])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f237])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    spl2_10 <=> v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.52  fof(f475,plain,(
% 0.21/0.52    v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_3 | ~spl2_6)),
% 0.21/0.52    inference(forward_demodulation,[],[f82,f124])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f81])).
% 0.21/0.52  fof(f469,plain,(
% 0.21/0.52    ~spl2_1 | ~spl2_4 | spl2_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f468])).
% 0.21/0.52  fof(f468,plain,(
% 0.21/0.52    $false | (~spl2_1 | ~spl2_4 | spl2_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f467,f42])).
% 0.21/0.52  fof(f467,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_4 | spl2_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f466,f381])).
% 0.21/0.52  fof(f381,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | (~spl2_1 | ~spl2_4 | spl2_5)),
% 0.21/0.52    inference(superposition,[],[f346,f349])).
% 0.21/0.52  fof(f349,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | (~spl2_1 | ~spl2_4 | spl2_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f348,f42])).
% 0.21/0.52  fof(f348,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_4 | spl2_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f347,f346])).
% 0.21/0.52  fof(f347,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f340,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f340,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~v2_pre_topc(sK0) | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f274,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    v2_compts_1(sK1,sK0) | ~spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    ~v2_compts_1(sK1,sK0) | k1_xboole_0 = sK1 | ~v2_pre_topc(sK0) | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f191,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0) | k1_xboole_0 = X1 | ~v2_pre_topc(X0) | v1_compts_1(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | (~spl2_4 | spl2_5)),
% 0.21/0.52    inference(forward_demodulation,[],[f119,f228])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f118])).
% 0.21/0.52  fof(f466,plain,(
% 0.21/0.52    v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_4 | spl2_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f454,f350])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    v2_compts_1(k1_xboole_0,sK0) | (~spl2_1 | ~spl2_4 | spl2_5)),
% 0.21/0.52    inference(superposition,[],[f74,f349])).
% 0.21/0.52  fof(f454,plain,(
% 0.21/0.52    ~v2_compts_1(k1_xboole_0,sK0) | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_4 | spl2_5)),
% 0.21/0.52    inference(resolution,[],[f360,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(k1_xboole_0,X0) | v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f360,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_4 | spl2_5)),
% 0.21/0.52    inference(superposition,[],[f191,f349])).
% 0.21/0.52  fof(f332,plain,(
% 0.21/0.52    ~spl2_4 | ~spl2_5 | spl2_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f331])).
% 0.21/0.52  fof(f331,plain,(
% 0.21/0.52    $false | (~spl2_4 | ~spl2_5 | spl2_6)),
% 0.21/0.52    inference(global_subsumption,[],[f47,f86,f191,f318,f322])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_4 | ~spl2_5 | spl2_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f321,f95])).
% 0.21/0.52  fof(f321,plain,(
% 0.21/0.52    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_4 | ~spl2_5 | spl2_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f320,f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f97,f42])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    inference(resolution,[],[f60,f41])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 0.21/0.52  fof(f320,plain,(
% 0.21/0.52    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_4 | ~spl2_5 | spl2_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f319,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_4 | ~spl2_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f126,f120])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | k1_xboole_0 = sK1 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f54,f86])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_compts_1(k1_pre_topc(X0,X1)) | k1_xboole_0 = X1 | ~v2_pre_topc(X0) | v2_compts_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f318,plain,(
% 0.21/0.52    v2_compts_1(sK1,sK0) | (~spl2_4 | ~spl2_5 | spl2_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f317,f42])).
% 0.21/0.52  fof(f317,plain,(
% 0.21/0.52    v2_compts_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_5 | spl2_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f279,f304])).
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    v1_compts_1(k1_pre_topc(sK0,sK1)) | (~spl2_4 | ~spl2_5)),
% 0.21/0.52    inference(superposition,[],[f120,f228])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_4 | spl2_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f278,f41])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_compts_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_4 | spl2_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f273,f123])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | k1_xboole_0 = sK1 | ~v2_pre_topc(sK0) | v2_compts_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f191,f54])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    spl2_9 | ~spl2_10 | ~spl2_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f220,f241,f237,f233])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f200,f95])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.52    inference(superposition,[],[f68,f181])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    spl2_2 | ~spl2_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f207])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    $false | (spl2_2 | ~spl2_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f191,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    spl2_5 | spl2_6 | ~spl2_3 | ~spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f116,f85,f81,f122,f118])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | (~spl2_3 | ~spl2_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f115,f95])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_3 | ~spl2_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f114,f98])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_3 | ~spl2_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f113,f82])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 = sK1 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.52    inference(resolution,[],[f53,f86])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl2_1 | spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f81,f73])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl2_2 | spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f46,f85,f77])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f47,f85,f81,f77,f73])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (5225)------------------------------
% 0.21/0.52  % (5225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5225)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (5225)Memory used [KB]: 11001
% 0.21/0.52  % (5225)Time elapsed: 0.095 s
% 0.21/0.52  % (5225)------------------------------
% 0.21/0.52  % (5225)------------------------------
% 0.21/0.52  % (5211)Success in time 0.161 s
%------------------------------------------------------------------------------
