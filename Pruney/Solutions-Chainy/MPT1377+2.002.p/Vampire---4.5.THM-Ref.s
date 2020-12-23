%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  196 (1848 expanded)
%              Number of leaves         :   24 ( 478 expanded)
%              Depth                    :   26
%              Number of atoms          :  796 (10654 expanded)
%              Number of equality atoms :   76 ( 460 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f614,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f86,f89,f104,f116,f128,f212,f236,f237,f310,f331,f345,f365,f377,f395,f400,f580,f609])).

fof(f609,plain,
    ( ~ spl2_2
    | spl2_4
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | ~ spl2_2
    | spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f75,f603])).

fof(f603,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f84,f183])).

fof(f183,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f180])).

fof(f180,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_6 ),
    inference(superposition,[],[f112,f103])).

fof(f103,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_6
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f112,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK0) = X2 ) ),
    inference(resolution,[],[f90,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f90,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f46,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f84,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f75,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f580,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(global_subsumption,[],[f401,f574])).

fof(f574,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f387,f559])).

fof(f559,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(superposition,[],[f227,f412])).

fof(f412,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(superposition,[],[f260,f127])).

fof(f127,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl2_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f260,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f259,f40])).

fof(f259,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f258,f200])).

fof(f200,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f83,f183])).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f258,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f164,f159])).

fof(f159,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f158,f154])).

fof(f154,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f147,f113])).

fof(f113,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f90,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f147,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f131,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f131,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f106,f113])).

fof(f106,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f64,f83])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f158,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f145,f40])).

fof(f145,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f131,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f163,f132])).

fof(f132,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f105,f113])).

fof(f105,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f63,f83])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
        | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_4 ),
    inference(superposition,[],[f67,f150])).

fof(f150,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f149,f113])).

fof(f149,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f148,f83])).

fof(f148,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f144,f132])).

fof(f144,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f131,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | k1_pre_topc(X0,k2_struct_0(X2)) = X2
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_pre_topc(X0,X1) = X2
      | k2_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f227,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl2_11
  <=> v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f387,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | v2_compts_1(k1_xboole_0,sK0)
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f379,f40])).

fof(f379,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | v2_compts_1(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_13 ),
    inference(resolution,[],[f234,f65])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f234,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl2_13
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f401,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | spl2_1
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f72,f127])).

fof(f72,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_1
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f400,plain,
    ( ~ spl2_3
    | ~ spl2_8
    | spl2_12 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_8
    | spl2_12 ),
    inference(subsumption_resolution,[],[f398,f231])).

fof(f231,plain,
    ( ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl2_12
  <=> v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f398,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f79,f127])).

fof(f79,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_3
  <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f395,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | spl2_7
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | spl2_7
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(global_subsumption,[],[f347,f348,f384])).

fof(f384,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f378,f40])).

fof(f378,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_13 ),
    inference(resolution,[],[f234,f66])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f348,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(superposition,[],[f71,f127])).

fof(f71,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f347,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_6
    | spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f346,f127])).

fof(f346,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_6
    | spl2_7 ),
    inference(forward_demodulation,[],[f122,f260])).

fof(f122,plain,
    ( ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl2_7
  <=> v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f377,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | spl2_7
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | spl2_7
    | spl2_8 ),
    inference(global_subsumption,[],[f369,f126])).

fof(f126,plain,
    ( k1_xboole_0 != sK1
    | spl2_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f369,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | spl2_7 ),
    inference(subsumption_resolution,[],[f368,f40])).

fof(f368,plain,
    ( k1_xboole_0 = sK1
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | spl2_7 ),
    inference(subsumption_resolution,[],[f367,f346])).

fof(f367,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f366,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f366,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_pre_topc(sK0)
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f262,f71])).

fof(f262,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | k1_xboole_0 = sK1
    | ~ v2_pre_topc(sK0)
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(resolution,[],[f200,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | v1_compts_1(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f365,plain,
    ( ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8
    | spl2_13 ),
    inference(subsumption_resolution,[],[f359,f235])).

fof(f235,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f233])).

fof(f359,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(superposition,[],[f200,f127])).

fof(f345,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f343,f230])).

fof(f230,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f229])).

fof(f343,plain,
    ( ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f80,f313])).

fof(f313,plain,
    ( k1_xboole_0 = sK1
    | spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f312,f113])).

fof(f312,plain,
    ( k1_xboole_0 = sK1
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f311,f80])).

fof(f311,plain,
    ( k1_xboole_0 = sK1
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f289,f94])).

fof(f94,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f93,f40])).

fof(f93,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f58,f39])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f289,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f110,f123])).

fof(f123,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f110,plain,
    ( ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | k1_xboole_0 = sK1
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f54,f83])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_compts_1(k1_pre_topc(X0,X1))
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | v2_compts_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f331,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | spl2_11 ),
    inference(subsumption_resolution,[],[f316,f226])).

fof(f226,plain,
    ( ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f225])).

fof(f316,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f123,f313])).

fof(f310,plain,
    ( ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | spl2_8 ),
    inference(global_subsumption,[],[f45,f83,f200,f288,f292])).

fof(f292,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4
    | ~ spl2_7
    | spl2_8 ),
    inference(subsumption_resolution,[],[f291,f113])).

fof(f291,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4
    | ~ spl2_7
    | spl2_8 ),
    inference(subsumption_resolution,[],[f290,f94])).

fof(f290,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4
    | ~ spl2_7
    | spl2_8 ),
    inference(subsumption_resolution,[],[f289,f126])).

fof(f288,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | spl2_8 ),
    inference(subsumption_resolution,[],[f287,f40])).

fof(f287,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | spl2_8 ),
    inference(subsumption_resolution,[],[f266,f271])).

fof(f271,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(superposition,[],[f123,f260])).

fof(f266,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_6
    | spl2_8 ),
    inference(subsumption_resolution,[],[f265,f39])).

fof(f265,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_6
    | spl2_8 ),
    inference(subsumption_resolution,[],[f261,f126])).

fof(f261,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | k1_xboole_0 = sK1
    | ~ v2_pre_topc(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(resolution,[],[f200,f54])).

fof(f45,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f237,plain,
    ( spl2_12
    | ~ spl2_11
    | ~ spl2_13
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f221,f101,f233,f225,f229])).

% (19714)Refutation not found, incomplete strategy% (19714)------------------------------
% (19714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19714)Termination reason: Refutation not found, incomplete strategy

% (19714)Memory used [KB]: 1663
% (19714)Time elapsed: 0.078 s
% (19714)------------------------------
% (19714)------------------------------
fof(f221,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f206,f113])).

fof(f206,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_6 ),
    inference(superposition,[],[f65,f183])).

fof(f236,plain,
    ( spl2_11
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f222,f101,f233,f229,f225])).

fof(f222,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f207,f113])).

fof(f207,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_6 ),
    inference(superposition,[],[f66,f183])).

fof(f212,plain,
    ( spl2_2
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl2_2
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f200,f76])).

fof(f76,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f128,plain,
    ( spl2_7
    | spl2_8
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f119,f82,f78,f125,f121])).

fof(f119,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f118,f113])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f117,f94])).

fof(f117,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f109,f79])).

fof(f109,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | k1_xboole_0 = sK1
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f53,f83])).

fof(f116,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f113,f99])).

fof(f99,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_5
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f104,plain,
    ( ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f95,f101,f97])).

fof(f95,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f92,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f92,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f91,f40])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f57,f39])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,
    ( spl2_1
    | spl2_3 ),
    inference(avatar_split_clause,[],[f41,f78,f70])).

fof(f41,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,
    ( spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f44,f82,f74])).

fof(f44,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f45,f82,f78,f74,f70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:22:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (19710)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (19716)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.49  % (19731)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (19713)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (19708)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (19725)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.49  % (19708)Refutation not found, incomplete strategy% (19708)------------------------------
% 0.21/0.49  % (19708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19708)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19708)Memory used [KB]: 10618
% 0.21/0.49  % (19708)Time elapsed: 0.087 s
% 0.21/0.49  % (19708)------------------------------
% 0.21/0.49  % (19708)------------------------------
% 0.21/0.49  % (19712)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (19728)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (19714)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (19709)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (19718)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (19729)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (19717)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (19727)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (19721)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (19722)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (19715)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (19730)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (19733)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (19711)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (19707)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (19723)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (19726)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (19720)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (19717)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (19732)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (19724)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f614,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f85,f86,f89,f104,f116,f128,f212,f236,f237,f310,f331,f345,f365,f377,f395,f400,f580,f609])).
% 0.21/0.53  fof(f609,plain,(
% 0.21/0.53    ~spl2_2 | spl2_4 | ~spl2_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f608])).
% 0.21/0.53  fof(f608,plain,(
% 0.21/0.53    $false | (~spl2_2 | spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f75,f603])).
% 0.21/0.53  fof(f603,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(forward_demodulation,[],[f84,f183])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_6),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_6),
% 0.21/0.53    inference(superposition,[],[f112,f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl2_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl2_6 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ( ! [X2,X3] : (g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = X2) )),
% 0.21/0.53    inference(resolution,[],[f90,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    inference(resolution,[],[f46,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_compts_1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f580,plain,(
% 0.21/0.53    spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_11 | ~spl2_13),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f579])).
% 0.21/0.53  fof(f579,plain,(
% 0.21/0.53    $false | (spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_11 | ~spl2_13)),
% 0.21/0.53    inference(global_subsumption,[],[f401,f574])).
% 0.21/0.53  fof(f574,plain,(
% 0.21/0.53    v2_compts_1(k1_xboole_0,sK0) | (~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_11 | ~spl2_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f387,f559])).
% 0.21/0.53  fof(f559,plain,(
% 0.21/0.53    v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | (~spl2_4 | ~spl2_6 | ~spl2_8 | ~spl2_11)),
% 0.21/0.53    inference(superposition,[],[f227,f412])).
% 0.21/0.53  fof(f412,plain,(
% 0.21/0.53    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0) | (~spl2_4 | ~spl2_6 | ~spl2_8)),
% 0.21/0.53    inference(superposition,[],[f260,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl2_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f125])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl2_8 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) | (~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f259,f40])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f258,f200])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(superposition,[],[f83,f183])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.53    inference(resolution,[],[f164,f159])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f158,f154])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f147,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.53    inference(resolution,[],[f90,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.53    inference(resolution,[],[f131,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f106,f113])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.53    inference(resolution,[],[f64,f83])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f40])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_4),
% 0.21/0.53    inference(resolution,[],[f131,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0)) ) | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f163,f132])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f105,f113])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.53    inference(resolution,[],[f63,f83])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X0,sK1) | ~l1_pre_topc(X0)) ) | ~spl2_4),
% 0.21/0.53    inference(superposition,[],[f67,f150])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f149,f113])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f148,f83])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f144,f132])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    sK1 = k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.53    inference(resolution,[],[f131,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | k1_pre_topc(X0,k2_struct_0(X2)) = X2 | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | ~spl2_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f225])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    spl2_11 <=> v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.53  fof(f387,plain,(
% 0.21/0.53    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | v2_compts_1(k1_xboole_0,sK0) | ~spl2_13),
% 0.21/0.53    inference(subsumption_resolution,[],[f379,f40])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | v2_compts_1(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | ~spl2_13),
% 0.21/0.53    inference(resolution,[],[f234,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | v2_compts_1(k1_xboole_0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1)) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & (((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f233])).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    spl2_13 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.53  fof(f401,plain,(
% 0.21/0.53    ~v2_compts_1(k1_xboole_0,sK0) | (spl2_1 | ~spl2_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f72,f127])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ~v2_compts_1(sK1,sK0) | spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    spl2_1 <=> v2_compts_1(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f400,plain,(
% 0.21/0.53    ~spl2_3 | ~spl2_8 | spl2_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f399])).
% 0.21/0.53  fof(f399,plain,(
% 0.21/0.53    $false | (~spl2_3 | ~spl2_8 | spl2_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f398,f231])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f229])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    spl2_12 <=> v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.53  fof(f398,plain,(
% 0.21/0.53    v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_3 | ~spl2_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f79,f127])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    spl2_3 <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f395,plain,(
% 0.21/0.53    ~spl2_1 | ~spl2_4 | ~spl2_6 | spl2_7 | ~spl2_8 | ~spl2_13),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f394])).
% 0.21/0.53  fof(f394,plain,(
% 0.21/0.53    $false | (~spl2_1 | ~spl2_4 | ~spl2_6 | spl2_7 | ~spl2_8 | ~spl2_13)),
% 0.21/0.53    inference(global_subsumption,[],[f347,f348,f384])).
% 0.21/0.53  fof(f384,plain,(
% 0.21/0.53    ~v2_compts_1(k1_xboole_0,sK0) | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | ~spl2_13),
% 0.21/0.53    inference(subsumption_resolution,[],[f378,f40])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    ~v2_compts_1(k1_xboole_0,sK0) | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | ~l1_pre_topc(sK0) | ~spl2_13),
% 0.21/0.53    inference(resolution,[],[f234,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(k1_xboole_0,X0) | v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f348,plain,(
% 0.21/0.53    v2_compts_1(k1_xboole_0,sK0) | (~spl2_1 | ~spl2_8)),
% 0.21/0.53    inference(superposition,[],[f71,f127])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    v2_compts_1(sK1,sK0) | ~spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f70])).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    ~v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | (~spl2_4 | ~spl2_6 | spl2_7 | ~spl2_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f346,f127])).
% 0.21/0.53  fof(f346,plain,(
% 0.21/0.53    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | (~spl2_4 | ~spl2_6 | spl2_7)),
% 0.21/0.53    inference(forward_demodulation,[],[f122,f260])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | spl2_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f121])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl2_7 <=> v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    ~spl2_1 | ~spl2_4 | ~spl2_6 | spl2_7 | spl2_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f376])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    $false | (~spl2_1 | ~spl2_4 | ~spl2_6 | spl2_7 | spl2_8)),
% 0.21/0.53    inference(global_subsumption,[],[f369,f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | spl2_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f125])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | (~spl2_1 | ~spl2_4 | ~spl2_6 | spl2_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f368,f40])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_4 | ~spl2_6 | spl2_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f367,f346])).
% 0.21/0.53  fof(f367,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f366,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f366,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~v2_pre_topc(sK0) | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f262,f71])).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    ~v2_compts_1(sK1,sK0) | k1_xboole_0 = sK1 | ~v2_pre_topc(sK0) | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(resolution,[],[f200,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0) | k1_xboole_0 = X1 | ~v2_pre_topc(X0) | v1_compts_1(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f365,plain,(
% 0.21/0.53    ~spl2_4 | ~spl2_6 | ~spl2_8 | spl2_13),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f364])).
% 0.21/0.53  fof(f364,plain,(
% 0.21/0.53    $false | (~spl2_4 | ~spl2_6 | ~spl2_8 | spl2_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f359,f235])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f233])).
% 0.21/0.53  fof(f359,plain,(
% 0.21/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | ~spl2_6 | ~spl2_8)),
% 0.21/0.53    inference(superposition,[],[f200,f127])).
% 0.21/0.53  fof(f345,plain,(
% 0.21/0.53    spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f344])).
% 0.21/0.53  fof(f344,plain,(
% 0.21/0.53    $false | (spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_12)),
% 0.21/0.53    inference(subsumption_resolution,[],[f343,f230])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f229])).
% 0.21/0.53  fof(f343,plain,(
% 0.21/0.53    ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl2_3 | ~spl2_4 | ~spl2_7)),
% 0.21/0.53    inference(superposition,[],[f80,f313])).
% 0.21/0.53  fof(f313,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | (spl2_3 | ~spl2_4 | ~spl2_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f312,f113])).
% 0.21/0.53  fof(f312,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl2_3 | ~spl2_4 | ~spl2_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f311,f80])).
% 0.21/0.53  fof(f311,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_4 | ~spl2_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f289,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f93,f40])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.53    inference(resolution,[],[f58,f39])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_4 | ~spl2_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f110,f123])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f121])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | k1_xboole_0 = sK1 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.53    inference(resolution,[],[f54,f83])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_compts_1(k1_pre_topc(X0,X1)) | k1_xboole_0 = X1 | ~v2_pre_topc(X0) | v2_compts_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f78])).
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    spl2_3 | ~spl2_4 | ~spl2_7 | spl2_11),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f330])).
% 0.21/0.53  fof(f330,plain,(
% 0.21/0.53    $false | (spl2_3 | ~spl2_4 | ~spl2_7 | spl2_11)),
% 0.21/0.53    inference(subsumption_resolution,[],[f316,f226])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | spl2_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f225])).
% 0.21/0.53  fof(f316,plain,(
% 0.21/0.53    v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | (spl2_3 | ~spl2_4 | ~spl2_7)),
% 0.21/0.53    inference(superposition,[],[f123,f313])).
% 0.21/0.53  fof(f310,plain,(
% 0.21/0.53    ~spl2_4 | ~spl2_6 | ~spl2_7 | spl2_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f309])).
% 0.21/0.53  fof(f309,plain,(
% 0.21/0.53    $false | (~spl2_4 | ~spl2_6 | ~spl2_7 | spl2_8)),
% 0.21/0.53    inference(global_subsumption,[],[f45,f83,f200,f288,f292])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_4 | ~spl2_7 | spl2_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f291,f113])).
% 0.21/0.53  fof(f291,plain,(
% 0.21/0.53    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_4 | ~spl2_7 | spl2_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f290,f94])).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_4 | ~spl2_7 | spl2_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f289,f126])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    v2_compts_1(sK1,sK0) | (~spl2_4 | ~spl2_6 | ~spl2_7 | spl2_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f287,f40])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    v2_compts_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_6 | ~spl2_7 | spl2_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f266,f271])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    v1_compts_1(k1_pre_topc(sK0,sK1)) | (~spl2_4 | ~spl2_6 | ~spl2_7)),
% 0.21/0.53    inference(superposition,[],[f123,f260])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_6 | spl2_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f265,f39])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_compts_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_6 | spl2_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f261,f126])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | k1_xboole_0 = sK1 | ~v2_pre_topc(sK0) | v2_compts_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(resolution,[],[f200,f54])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    spl2_12 | ~spl2_11 | ~spl2_13 | ~spl2_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f221,f101,f233,f225,f229])).
% 0.21/0.53  % (19714)Refutation not found, incomplete strategy% (19714)------------------------------
% 0.21/0.53  % (19714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19714)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19714)Memory used [KB]: 1663
% 0.21/0.53  % (19714)Time elapsed: 0.078 s
% 0.21/0.53  % (19714)------------------------------
% 0.21/0.53  % (19714)------------------------------
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f206,f113])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_6),
% 0.21/0.53    inference(superposition,[],[f65,f183])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    spl2_11 | ~spl2_12 | ~spl2_13 | ~spl2_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f222,f101,f233,f229,f225])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | ~spl2_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f207,f113])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_6),
% 0.21/0.53    inference(superposition,[],[f66,f183])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    spl2_2 | ~spl2_4 | ~spl2_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    $false | (spl2_2 | ~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f200,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f74])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    spl2_7 | spl2_8 | ~spl2_3 | ~spl2_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f119,f82,f78,f125,f121])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | (~spl2_3 | ~spl2_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f118,f113])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_3 | ~spl2_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f117,f94])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_3 | ~spl2_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f109,f79])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 = sK1 | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.53    inference(resolution,[],[f53,f83])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl2_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    $false | spl2_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f113,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl2_5 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ~spl2_5 | spl2_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f95,f101,f97])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.53    inference(resolution,[],[f92,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f91,f40])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.53    inference(resolution,[],[f57,f39])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    spl2_1 | spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f78,f70])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl2_2 | spl2_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f82,f74])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f82,f78,f74,f70])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (19717)------------------------------
% 0.21/0.53  % (19717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19717)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (19717)Memory used [KB]: 11001
% 0.21/0.53  % (19717)Time elapsed: 0.122 s
% 0.21/0.53  % (19717)------------------------------
% 0.21/0.53  % (19717)------------------------------
% 0.21/0.54  % (19704)Success in time 0.179 s
%------------------------------------------------------------------------------
