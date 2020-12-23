%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1221+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:13 EST 2020

% Result     : Theorem 6.35s
% Output     : Refutation 6.35s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 231 expanded)
%              Number of leaves         :   11 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  180 ( 969 expanded)
%              Number of equality atoms :   11 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4032,f4056,f6567,f7227])).

fof(f7227,plain,
    ( ~ spl101_1
    | spl101_2 ),
    inference(avatar_contradiction_clause,[],[f7226])).

fof(f7226,plain,
    ( $false
    | ~ spl101_1
    | spl101_2 ),
    inference(subsumption_resolution,[],[f7225,f3721])).

fof(f3721,plain,(
    m1_subset_1(u1_struct_0(sK21),k1_zfmisc_1(u1_struct_0(sK21))) ),
    inference(backward_demodulation,[],[f3694,f3695])).

fof(f3695,plain,(
    u1_struct_0(sK21) = k2_struct_0(sK21) ),
    inference(resolution,[],[f3665,f3060])).

fof(f3060,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2270])).

fof(f2270,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3665,plain,(
    l1_struct_0(sK21) ),
    inference(resolution,[],[f2840,f3191])).

fof(f3191,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2331])).

fof(f2331,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2840,plain,(
    l1_pre_topc(sK21) ),
    inference(cnf_transformation,[],[f2566])).

fof(f2566,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK21),sK22),sK21)
      | ~ v4_pre_topc(sK22,sK21) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK21),sK22),sK21)
      | v4_pre_topc(sK22,sK21) )
    & m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK21)))
    & l1_pre_topc(sK21) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21,sK22])],[f2563,f2565,f2564])).

fof(f2564,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK21),X1),sK21)
            | ~ v4_pre_topc(X1,sK21) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK21),X1),sK21)
            | v4_pre_topc(X1,sK21) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK21))) )
      & l1_pre_topc(sK21) ) ),
    introduced(choice_axiom,[])).

fof(f2565,plain,
    ( ? [X1] :
        ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK21),X1),sK21)
          | ~ v4_pre_topc(X1,sK21) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK21),X1),sK21)
          | v4_pre_topc(X1,sK21) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK21))) )
   => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK21),sK22),sK21)
        | ~ v4_pre_topc(sK22,sK21) )
      & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK21),sK22),sK21)
        | v4_pre_topc(sK22,sK21) )
      & m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK21))) ) ),
    introduced(choice_axiom,[])).

fof(f2563,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2562])).

fof(f2562,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2097])).

fof(f2097,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2089])).

fof(f2089,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f2088])).

fof(f2088,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f3694,plain,(
    m1_subset_1(k2_struct_0(sK21),k1_zfmisc_1(u1_struct_0(sK21))) ),
    inference(resolution,[],[f3665,f3059])).

fof(f3059,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2269])).

fof(f2269,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1781])).

fof(f1781,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f7225,plain,
    ( ~ m1_subset_1(u1_struct_0(sK21),k1_zfmisc_1(u1_struct_0(sK21)))
    | ~ spl101_1
    | spl101_2 ),
    inference(subsumption_resolution,[],[f7210,f4055])).

fof(f4055,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK21),sK22),sK21)
    | spl101_2 ),
    inference(avatar_component_clause,[],[f4030])).

fof(f4030,plain,
    ( spl101_2
  <=> v3_pre_topc(k4_xboole_0(u1_struct_0(sK21),sK22),sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_2])])).

fof(f7210,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK21),sK22),sK21)
    | ~ m1_subset_1(u1_struct_0(sK21),k1_zfmisc_1(u1_struct_0(sK21)))
    | ~ spl101_1 ),
    inference(superposition,[],[f7051,f3042])).

fof(f3042,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2253])).

fof(f2253,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f494])).

fof(f494,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f7051,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK21),u1_struct_0(sK21),sK22),sK21)
    | ~ spl101_1 ),
    inference(forward_demodulation,[],[f7050,f3695])).

fof(f7050,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK21),k2_struct_0(sK21),sK22),sK21)
    | ~ spl101_1 ),
    inference(subsumption_resolution,[],[f7049,f2840])).

fof(f7049,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK21),k2_struct_0(sK21),sK22),sK21)
    | ~ l1_pre_topc(sK21)
    | ~ spl101_1 ),
    inference(subsumption_resolution,[],[f7039,f2841])).

fof(f2841,plain,(
    m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK21))) ),
    inference(cnf_transformation,[],[f2566])).

fof(f7039,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK21),k2_struct_0(sK21),sK22),sK21)
    | ~ m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK21)))
    | ~ l1_pre_topc(sK21)
    | ~ spl101_1 ),
    inference(resolution,[],[f4028,f2871])).

fof(f2871,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2588])).

fof(f2588,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2106])).

fof(f2106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1775])).

fof(f1775,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f4028,plain,
    ( v4_pre_topc(sK22,sK21)
    | ~ spl101_1 ),
    inference(avatar_component_clause,[],[f4027])).

fof(f4027,plain,
    ( spl101_1
  <=> v4_pre_topc(sK22,sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_1])])).

fof(f6567,plain,
    ( spl101_1
    | ~ spl101_2 ),
    inference(avatar_contradiction_clause,[],[f6566])).

fof(f6566,plain,
    ( $false
    | spl101_1
    | ~ spl101_2 ),
    inference(subsumption_resolution,[],[f6565,f3721])).

fof(f6565,plain,
    ( ~ m1_subset_1(u1_struct_0(sK21),k1_zfmisc_1(u1_struct_0(sK21)))
    | spl101_1
    | ~ spl101_2 ),
    inference(subsumption_resolution,[],[f6552,f4031])).

fof(f4031,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK21),sK22),sK21)
    | ~ spl101_2 ),
    inference(avatar_component_clause,[],[f4030])).

fof(f6552,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK21),sK22),sK21)
    | ~ m1_subset_1(u1_struct_0(sK21),k1_zfmisc_1(u1_struct_0(sK21)))
    | spl101_1 ),
    inference(superposition,[],[f4068,f3042])).

fof(f4068,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK21),u1_struct_0(sK21),sK22),sK21)
    | spl101_1 ),
    inference(forward_demodulation,[],[f4067,f3695])).

fof(f4067,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK21),k2_struct_0(sK21),sK22),sK21)
    | spl101_1 ),
    inference(subsumption_resolution,[],[f4066,f2840])).

fof(f4066,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK21),k2_struct_0(sK21),sK22),sK21)
    | ~ l1_pre_topc(sK21)
    | spl101_1 ),
    inference(subsumption_resolution,[],[f4060,f2841])).

fof(f4060,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK21),k2_struct_0(sK21),sK22),sK21)
    | ~ m1_subset_1(sK22,k1_zfmisc_1(u1_struct_0(sK21)))
    | ~ l1_pre_topc(sK21)
    | spl101_1 ),
    inference(resolution,[],[f4054,f2872])).

fof(f2872,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2588])).

fof(f4054,plain,
    ( ~ v4_pre_topc(sK22,sK21)
    | spl101_1 ),
    inference(avatar_component_clause,[],[f4027])).

fof(f4056,plain,
    ( ~ spl101_1
    | ~ spl101_2 ),
    inference(avatar_split_clause,[],[f3982,f4030,f4027])).

fof(f3982,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK21),sK22),sK21)
    | ~ v4_pre_topc(sK22,sK21) ),
    inference(backward_demodulation,[],[f2843,f3826])).

fof(f3826,plain,(
    k3_subset_1(u1_struct_0(sK21),sK22) = k4_xboole_0(u1_struct_0(sK21),sK22) ),
    inference(resolution,[],[f2841,f2899])).

fof(f2899,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2132])).

fof(f2132,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2843,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK21),sK22),sK21)
    | ~ v4_pre_topc(sK22,sK21) ),
    inference(cnf_transformation,[],[f2566])).

fof(f4032,plain,
    ( spl101_1
    | spl101_2 ),
    inference(avatar_split_clause,[],[f3981,f4030,f4027])).

fof(f3981,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK21),sK22),sK21)
    | v4_pre_topc(sK22,sK21) ),
    inference(backward_demodulation,[],[f2842,f3826])).

fof(f2842,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK21),sK22),sK21)
    | v4_pre_topc(sK22,sK21) ),
    inference(cnf_transformation,[],[f2566])).
%------------------------------------------------------------------------------
