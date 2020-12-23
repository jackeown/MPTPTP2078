%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1876+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:36 EST 2020

% Result     : Theorem 26.61s
% Output     : Refutation 26.61s
% Verified   : 
% Statistics : Number of formulae       :  117 (1758 expanded)
%              Number of leaves         :   14 ( 478 expanded)
%              Depth                    :   23
%              Number of atoms          :  543 (15049 expanded)
%              Number of equality atoms :   17 ( 216 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48503,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48287,f31362])).

fof(f31362,plain,(
    ~ l1_struct_0(sK170(sK74,sK75)) ),
    inference(global_subsumption,[],[f5310,f25014,f25374,f31360,f31361])).

fof(f31361,plain,
    ( ~ v1_zfmisc_1(sK75)
    | ~ l1_struct_0(sK170(sK74,sK75)) ),
    inference(subsumption_resolution,[],[f30779,f31360])).

fof(f30779,plain,
    ( ~ v1_zfmisc_1(sK75)
    | ~ l1_struct_0(sK170(sK74,sK75))
    | v7_struct_0(sK170(sK74,sK75)) ),
    inference(superposition,[],[f5324,f8536])).

fof(f8536,plain,(
    sK75 = u1_struct_0(sK170(sK74,sK75)) ),
    inference(subsumption_resolution,[],[f8535,f5304])).

fof(f5304,plain,(
    ~ v2_struct_0(sK74) ),
    inference(cnf_transformation,[],[f4610])).

fof(f4610,plain,
    ( ( ~ v1_zfmisc_1(sK75)
      | ~ v2_tex_2(sK75,sK74) )
    & ( v1_zfmisc_1(sK75)
      | v2_tex_2(sK75,sK74) )
    & m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74)))
    & ~ v1_xboole_0(sK75)
    & l1_pre_topc(sK74)
    & v2_tdlat_3(sK74)
    & v2_pre_topc(sK74)
    & ~ v2_struct_0(sK74) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK74,sK75])],[f4607,f4609,f4608])).

fof(f4608,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK74) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK74) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK74)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK74)
      & v2_tdlat_3(sK74)
      & v2_pre_topc(sK74)
      & ~ v2_struct_0(sK74) ) ),
    introduced(choice_axiom,[])).

fof(f4609,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK74) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK74) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK74)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK75)
        | ~ v2_tex_2(sK75,sK74) )
      & ( v1_zfmisc_1(sK75)
        | v2_tex_2(sK75,sK74) )
      & m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74)))
      & ~ v1_xboole_0(sK75) ) ),
    introduced(choice_axiom,[])).

fof(f4607,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4606])).

fof(f4606,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3717])).

fof(f3717,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3716])).

fof(f3716,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3692])).

fof(f3692,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3691])).

fof(f3691,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f8535,plain,
    ( sK75 = u1_struct_0(sK170(sK74,sK75))
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f8534,f5307])).

fof(f5307,plain,(
    l1_pre_topc(sK74) ),
    inference(cnf_transformation,[],[f4610])).

fof(f8534,plain,
    ( sK75 = u1_struct_0(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f8246,f5308])).

fof(f5308,plain,(
    ~ v1_xboole_0(sK75) ),
    inference(cnf_transformation,[],[f4610])).

fof(f8246,plain,
    ( sK75 = u1_struct_0(sK170(sK74,sK75))
    | v1_xboole_0(sK75)
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f5309,f5954])).

fof(f5954,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK170(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4887])).

fof(f4887,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK170(X0,X1)) = X1
            & m1_pre_topc(sK170(X0,X1),X0)
            & v1_pre_topc(sK170(X0,X1))
            & ~ v2_struct_0(sK170(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK170])],[f4069,f4886])).

fof(f4886,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK170(X0,X1)) = X1
        & m1_pre_topc(sK170(X0,X1),X0)
        & v1_pre_topc(sK170(X0,X1))
        & ~ v2_struct_0(sK170(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4069,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4068])).

fof(f4068,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3653])).

fof(f3653,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f5309,plain,(
    m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74))) ),
    inference(cnf_transformation,[],[f4610])).

fof(f5324,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3731])).

fof(f3731,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f3730])).

fof(f3730,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1802])).

fof(f1802,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f31360,plain,
    ( ~ l1_struct_0(sK170(sK74,sK75))
    | ~ v7_struct_0(sK170(sK74,sK75)) ),
    inference(global_subsumption,[],[f5311,f25021,f25024,f25368,f30777])).

fof(f30777,plain,
    ( v1_zfmisc_1(sK75)
    | ~ l1_struct_0(sK170(sK74,sK75))
    | ~ v7_struct_0(sK170(sK74,sK75)) ),
    inference(superposition,[],[f5317,f8536])).

fof(f5317,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3721])).

fof(f3721,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f3720])).

fof(f3720,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1804])).

fof(f1804,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f25368,plain,
    ( v2_tex_2(sK75,sK74)
    | ~ v1_tdlat_3(sK170(sK74,sK75)) ),
    inference(subsumption_resolution,[],[f25367,f5309])).

fof(f25367,plain,
    ( ~ m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74)))
    | v2_tex_2(sK75,sK74)
    | ~ v1_tdlat_3(sK170(sK74,sK75)) ),
    inference(forward_demodulation,[],[f25366,f8536])).

fof(f25366,plain,
    ( v2_tex_2(sK75,sK74)
    | ~ v1_tdlat_3(sK170(sK74,sK75))
    | ~ m1_subset_1(u1_struct_0(sK170(sK74,sK75)),k1_zfmisc_1(u1_struct_0(sK74))) ),
    inference(forward_demodulation,[],[f25365,f8536])).

fof(f25365,plain,
    ( v2_tex_2(u1_struct_0(sK170(sK74,sK75)),sK74)
    | ~ v1_tdlat_3(sK170(sK74,sK75))
    | ~ m1_subset_1(u1_struct_0(sK170(sK74,sK75)),k1_zfmisc_1(u1_struct_0(sK74))) ),
    inference(subsumption_resolution,[],[f25364,f5304])).

fof(f25364,plain,
    ( v2_tex_2(u1_struct_0(sK170(sK74,sK75)),sK74)
    | ~ v1_tdlat_3(sK170(sK74,sK75))
    | ~ m1_subset_1(u1_struct_0(sK170(sK74,sK75)),k1_zfmisc_1(u1_struct_0(sK74)))
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f25363,f5307])).

fof(f25363,plain,
    ( v2_tex_2(u1_struct_0(sK170(sK74,sK75)),sK74)
    | ~ v1_tdlat_3(sK170(sK74,sK75))
    | ~ m1_subset_1(u1_struct_0(sK170(sK74,sK75)),k1_zfmisc_1(u1_struct_0(sK74)))
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f24996,f8527])).

fof(f8527,plain,(
    ~ v2_struct_0(sK170(sK74,sK75)) ),
    inference(subsumption_resolution,[],[f8526,f5304])).

fof(f8526,plain,
    ( ~ v2_struct_0(sK170(sK74,sK75))
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f8525,f5307])).

fof(f8525,plain,
    ( ~ v2_struct_0(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f8243,f5308])).

fof(f8243,plain,
    ( ~ v2_struct_0(sK170(sK74,sK75))
    | v1_xboole_0(sK75)
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f5309,f5951])).

fof(f5951,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK170(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4887])).

fof(f24996,plain,
    ( v2_tex_2(u1_struct_0(sK170(sK74,sK75)),sK74)
    | ~ v1_tdlat_3(sK170(sK74,sK75))
    | ~ m1_subset_1(u1_struct_0(sK170(sK74,sK75)),k1_zfmisc_1(u1_struct_0(sK74)))
    | v2_struct_0(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f8533,f6942])).

fof(f6942,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f5359])).

fof(f5359,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4631])).

fof(f4631,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3761])).

fof(f3761,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3760])).

fof(f3760,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3671])).

fof(f3671,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f8533,plain,(
    m1_pre_topc(sK170(sK74,sK75),sK74) ),
    inference(subsumption_resolution,[],[f8532,f5304])).

fof(f8532,plain,
    ( m1_pre_topc(sK170(sK74,sK75),sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f8531,f5307])).

fof(f8531,plain,
    ( m1_pre_topc(sK170(sK74,sK75),sK74)
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f8245,f5308])).

fof(f8245,plain,
    ( m1_pre_topc(sK170(sK74,sK75),sK74)
    | v1_xboole_0(sK75)
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f5309,f5953])).

fof(f5953,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK170(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4887])).

fof(f25024,plain,(
    v2_pre_topc(sK170(sK74,sK75)) ),
    inference(subsumption_resolution,[],[f25023,f5304])).

fof(f25023,plain,
    ( v2_pre_topc(sK170(sK74,sK75))
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f25022,f5307])).

fof(f25022,plain,
    ( v2_pre_topc(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f24892,f25018])).

fof(f25018,plain,(
    v2_tdlat_3(sK170(sK74,sK75)) ),
    inference(subsumption_resolution,[],[f25017,f5304])).

fof(f25017,plain,
    ( v2_tdlat_3(sK170(sK74,sK75))
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f25016,f5305])).

fof(f5305,plain,(
    v2_pre_topc(sK74) ),
    inference(cnf_transformation,[],[f4610])).

fof(f25016,plain,
    ( v2_tdlat_3(sK170(sK74,sK75))
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f25015,f5306])).

fof(f5306,plain,(
    v2_tdlat_3(sK74) ),
    inference(cnf_transformation,[],[f4610])).

fof(f25015,plain,
    ( v2_tdlat_3(sK170(sK74,sK75))
    | ~ v2_tdlat_3(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f24886,f5307])).

fof(f24886,plain,
    ( v2_tdlat_3(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74)
    | ~ v2_tdlat_3(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f8533,f5487])).

fof(f5487,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3813])).

fof(f3813,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3812])).

fof(f3812,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3590])).

fof(f3590,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f24892,plain,
    ( v2_pre_topc(sK170(sK74,sK75))
    | ~ v2_tdlat_3(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f8533,f5497])).

fof(f5497,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3823])).

fof(f3823,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3822])).

fof(f3822,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3551])).

fof(f3551,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v2_tdlat_3(X1)
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc15_tex_2)).

fof(f25021,plain,
    ( v1_tdlat_3(sK170(sK74,sK75))
    | ~ v2_pre_topc(sK170(sK74,sK75))
    | ~ v7_struct_0(sK170(sK74,sK75)) ),
    inference(subsumption_resolution,[],[f25020,f5304])).

fof(f25020,plain,
    ( v1_tdlat_3(sK170(sK74,sK75))
    | ~ v2_pre_topc(sK170(sK74,sK75))
    | ~ v7_struct_0(sK170(sK74,sK75))
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f25019,f5307])).

fof(f25019,plain,
    ( v1_tdlat_3(sK170(sK74,sK75))
    | ~ v2_pre_topc(sK170(sK74,sK75))
    | ~ v7_struct_0(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f24887,f8527])).

fof(f24887,plain,
    ( v1_tdlat_3(sK170(sK74,sK75))
    | ~ v2_pre_topc(sK170(sK74,sK75))
    | ~ v7_struct_0(sK170(sK74,sK75))
    | v2_struct_0(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f8533,f5489])).

fof(f5489,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3815])).

fof(f3815,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3814])).

fof(f3814,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3565])).

fof(f3565,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v2_tdlat_3(X1)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).

fof(f5311,plain,
    ( ~ v1_zfmisc_1(sK75)
    | ~ v2_tex_2(sK75,sK74) ),
    inference(cnf_transformation,[],[f4610])).

fof(f25374,plain,
    ( ~ v2_tex_2(sK75,sK74)
    | v1_tdlat_3(sK170(sK74,sK75)) ),
    inference(subsumption_resolution,[],[f25373,f5309])).

fof(f25373,plain,
    ( ~ m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74)))
    | ~ v2_tex_2(sK75,sK74)
    | v1_tdlat_3(sK170(sK74,sK75)) ),
    inference(forward_demodulation,[],[f25372,f8536])).

fof(f25372,plain,
    ( ~ v2_tex_2(sK75,sK74)
    | v1_tdlat_3(sK170(sK74,sK75))
    | ~ m1_subset_1(u1_struct_0(sK170(sK74,sK75)),k1_zfmisc_1(u1_struct_0(sK74))) ),
    inference(forward_demodulation,[],[f25371,f8536])).

fof(f25371,plain,
    ( v1_tdlat_3(sK170(sK74,sK75))
    | ~ v2_tex_2(u1_struct_0(sK170(sK74,sK75)),sK74)
    | ~ m1_subset_1(u1_struct_0(sK170(sK74,sK75)),k1_zfmisc_1(u1_struct_0(sK74))) ),
    inference(subsumption_resolution,[],[f25370,f5304])).

fof(f25370,plain,
    ( v1_tdlat_3(sK170(sK74,sK75))
    | ~ v2_tex_2(u1_struct_0(sK170(sK74,sK75)),sK74)
    | ~ m1_subset_1(u1_struct_0(sK170(sK74,sK75)),k1_zfmisc_1(u1_struct_0(sK74)))
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f25369,f5307])).

fof(f25369,plain,
    ( v1_tdlat_3(sK170(sK74,sK75))
    | ~ v2_tex_2(u1_struct_0(sK170(sK74,sK75)),sK74)
    | ~ m1_subset_1(u1_struct_0(sK170(sK74,sK75)),k1_zfmisc_1(u1_struct_0(sK74)))
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f24997,f8527])).

fof(f24997,plain,
    ( v1_tdlat_3(sK170(sK74,sK75))
    | ~ v2_tex_2(u1_struct_0(sK170(sK74,sK75)),sK74)
    | ~ m1_subset_1(u1_struct_0(sK170(sK74,sK75)),k1_zfmisc_1(u1_struct_0(sK74)))
    | v2_struct_0(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f8533,f6943])).

fof(f6943,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f5358])).

fof(f5358,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4631])).

fof(f25014,plain,
    ( v7_struct_0(sK170(sK74,sK75))
    | ~ v1_tdlat_3(sK170(sK74,sK75)) ),
    inference(subsumption_resolution,[],[f25013,f5304])).

fof(f25013,plain,
    ( v7_struct_0(sK170(sK74,sK75))
    | ~ v1_tdlat_3(sK170(sK74,sK75))
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f25012,f5305])).

fof(f25012,plain,
    ( v7_struct_0(sK170(sK74,sK75))
    | ~ v1_tdlat_3(sK170(sK74,sK75))
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f25011,f5306])).

fof(f25011,plain,
    ( v7_struct_0(sK170(sK74,sK75))
    | ~ v1_tdlat_3(sK170(sK74,sK75))
    | ~ v2_tdlat_3(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f25010,f5307])).

fof(f25010,plain,
    ( v7_struct_0(sK170(sK74,sK75))
    | ~ v1_tdlat_3(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74)
    | ~ v2_tdlat_3(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f24884,f8527])).

fof(f24884,plain,
    ( v7_struct_0(sK170(sK74,sK75))
    | ~ v1_tdlat_3(sK170(sK74,sK75))
    | v2_struct_0(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74)
    | ~ v2_tdlat_3(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f8533,f5484])).

fof(f5484,plain,(
    ! [X0,X1] :
      ( v7_struct_0(X1)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3809])).

fof(f3809,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3808])).

fof(f3808,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3575])).

fof(f3575,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => ( v7_struct_0(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc31_tex_2)).

fof(f5310,plain,
    ( v1_zfmisc_1(sK75)
    | v2_tex_2(sK75,sK74) ),
    inference(cnf_transformation,[],[f4610])).

fof(f48287,plain,(
    l1_struct_0(sK170(sK74,sK75)) ),
    inference(resolution,[],[f25080,f5627])).

fof(f5627,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3880])).

fof(f3880,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f25080,plain,(
    l1_pre_topc(sK170(sK74,sK75)) ),
    inference(subsumption_resolution,[],[f24914,f5307])).

fof(f24914,plain,
    ( l1_pre_topc(sK170(sK74,sK75))
    | ~ l1_pre_topc(sK74) ),
    inference(resolution,[],[f8533,f5920])).

fof(f5920,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4048])).

fof(f4048,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
%------------------------------------------------------------------------------
