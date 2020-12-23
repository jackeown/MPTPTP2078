%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1971+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:59 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  223 (2706 expanded)
%              Number of leaves         :   37 ( 843 expanded)
%              Depth                    :   18
%              Number of atoms          : 1297 (49309 expanded)
%              Number of equality atoms :   22 (  62 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f941,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f177,f178,f181,f184,f190,f193,f196,f334,f350,f400,f747,f751,f776,f781,f783,f785,f787,f789,f791,f933,f936,f938,f940])).

fof(f940,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f939])).

fof(f939,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4
    | spl6_9 ),
    inference(subsumption_resolution,[],[f834,f176])).

fof(f176,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f834,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f143,f155,f74,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_7)).

fof(f74,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
      | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
      | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
      | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_waybel_7(sK1,sK0)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
        & v2_waybel_7(sK1,k7_lattice3(sK0))
        & v13_waybel_0(sK1,k7_lattice3(sK0))
        & v2_waybel_0(sK1,k7_lattice3(sK0))
        & ~ v1_xboole_0(sK1) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v1_waybel_7(sK1,sK0)
        & v12_waybel_0(sK1,sK0)
        & v1_waybel_0(sK1,sK0)
        & ~ v1_xboole_0(sK1) ) )
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              | ~ v2_waybel_7(X1,k7_lattice3(X0))
              | ~ v13_waybel_0(X1,k7_lattice3(X0))
              | ~ v2_waybel_0(X1,k7_lattice3(X0))
              | v1_xboole_0(X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_waybel_7(X1,X0)
              | ~ v12_waybel_0(X1,X0)
              | ~ v1_waybel_0(X1,X0)
              | v1_xboole_0(X1) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
                & v2_waybel_7(X1,k7_lattice3(X0))
                & v13_waybel_0(X1,k7_lattice3(X0))
                & v2_waybel_0(X1,k7_lattice3(X0))
                & ~ v1_xboole_0(X1) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X1,X0)
                & v12_waybel_0(X1,X0)
                & v1_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) ) ) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
            | ~ v2_waybel_7(X1,k7_lattice3(sK0))
            | ~ v13_waybel_0(X1,k7_lattice3(sK0))
            | ~ v2_waybel_0(X1,k7_lattice3(sK0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v1_waybel_7(X1,sK0)
            | ~ v12_waybel_0(X1,sK0)
            | ~ v1_waybel_0(X1,sK0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
              & v2_waybel_7(X1,k7_lattice3(sK0))
              & v13_waybel_0(X1,k7_lattice3(sK0))
              & v2_waybel_0(X1,k7_lattice3(sK0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v1_waybel_7(X1,sK0)
              & v12_waybel_0(X1,sK0)
              & v1_waybel_0(X1,sK0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
          | ~ v2_waybel_7(X1,k7_lattice3(sK0))
          | ~ v13_waybel_0(X1,k7_lattice3(sK0))
          | ~ v2_waybel_0(X1,k7_lattice3(sK0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v1_waybel_7(X1,sK0)
          | ~ v12_waybel_0(X1,sK0)
          | ~ v1_waybel_0(X1,sK0)
          | v1_xboole_0(X1) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
            & v2_waybel_7(X1,k7_lattice3(sK0))
            & v13_waybel_0(X1,k7_lattice3(sK0))
            & v2_waybel_0(X1,k7_lattice3(sK0))
            & ~ v1_xboole_0(X1) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & v1_waybel_7(X1,sK0)
            & v12_waybel_0(X1,sK0)
            & v1_waybel_0(X1,sK0)
            & ~ v1_xboole_0(X1) ) ) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
        | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_7(sK1,sK0)
        | ~ v12_waybel_0(sK1,sK0)
        | ~ v1_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1) )
      & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
          & v2_waybel_7(sK1,k7_lattice3(sK0))
          & v13_waybel_0(sK1,k7_lattice3(sK0))
          & v2_waybel_0(sK1,k7_lattice3(sK0))
          & ~ v1_xboole_0(sK1) )
        | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v1_waybel_7(sK1,sK0)
          & v12_waybel_0(sK1,sK0)
          & v1_waybel_0(sK1,sK0)
          & ~ v1_xboole_0(sK1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_7)).

fof(f155,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f143,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl6_1
  <=> v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f938,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f937])).

fof(f937,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | spl6_7 ),
    inference(subsumption_resolution,[],[f837,f168])).

fof(f168,plain,
    ( ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl6_7
  <=> v13_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f837,plain,
    ( v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f147,f155,f74,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v13_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v13_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v13_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow_7)).

fof(f147,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_2
  <=> v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f936,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f935])).

fof(f935,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f833,f164])).

fof(f164,plain,
    ( ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl6_6
  <=> v2_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f833,plain,
    ( v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f143,f155,f74,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f933,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f932])).

fof(f932,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f919,f922])).

fof(f922,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f73,f74,f139,f143,f147,f866,f884,f151,f155,f865,f912,f117])).

fof(f117,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v1_waybel_7(X1,X0)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_hidden(X5,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & ~ r2_hidden(sK2(X0,X1),X1)
                & r2_hidden(k12_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f60,f62,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK2(X0,X1),X1)
            & r2_hidden(k12_lattice3(X0,sK2(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(k12_lattice3(X0,sK2(X0,X1),X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(k12_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_7)).

fof(f912,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f902,f903])).

fof(f903,plain,
    ( sK4(k7_lattice3(sK0),sK1) = k9_lattice3(sK0,sK4(k7_lattice3(sK0),sK1))
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f74,f780,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | k9_lattice3(X0,X1) = X1
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
         => k9_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattice3)).

fof(f780,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f778])).

fof(f778,plain,
    ( spl6_32
  <=> m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f902,plain,
    ( m1_subset_1(k9_lattice3(sK0,sK4(k7_lattice3(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f74,f780,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_lattice3)).

fof(f865,plain,
    ( ~ r2_hidden(sK4(k7_lattice3(sK0),sK1),sK1)
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f139,f214,f216,f211,f203,f172,f163,f167,f175,f222,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK5(X0,X1),X1)
                & ~ r2_hidden(sK4(X0,X1),X1)
                & r2_hidden(k13_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f65,f67,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k13_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK4(X0,X1),X1)
            & r2_hidden(k13_lattice3(X0,sK4(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(k13_lattice3(X0,sK4(X0,X1),X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(k13_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_7)).

fof(f222,plain,(
    v4_orders_2(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f70,f74,f134])).

fof(f134,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_yellow_7)).

fof(f175,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f174])).

fof(f167,plain,
    ( v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f166])).

fof(f163,plain,
    ( v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f172,plain,
    ( ~ v2_waybel_7(sK1,k7_lattice3(sK0))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl6_8
  <=> v2_waybel_7(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f203,plain,(
    l1_orders_2(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f74,f102])).

fof(f102,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f211,plain,(
    v1_lattice3(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f73,f74,f115])).

fof(f115,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_7)).

fof(f216,plain,(
    v5_orders_2(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f71,f74,f132])).

fof(f132,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_yellow_7)).

fof(f214,plain,(
    v3_orders_2(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f69,f74,f130])).

fof(f130,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_yellow_7)).

fof(f151,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_3
  <=> v1_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f884,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f874,f875])).

fof(f875,plain,
    ( sK5(k7_lattice3(sK0),sK1) = k9_lattice3(sK0,sK5(k7_lattice3(sK0),sK1))
    | ~ spl6_31 ),
    inference(unit_resulting_resolution,[],[f74,f775,f105])).

fof(f775,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f773])).

fof(f773,plain,
    ( spl6_31
  <=> m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f874,plain,
    ( m1_subset_1(k9_lattice3(sK0,sK5(k7_lattice3(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl6_31 ),
    inference(unit_resulting_resolution,[],[f74,f775,f138])).

fof(f866,plain,
    ( ~ r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f139,f214,f216,f211,f203,f172,f163,f167,f175,f222,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f139,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f73,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f71,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f70,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f69,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f919,plain,
    ( r2_hidden(k12_lattice3(sK0,sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f864,f918])).

fof(f918,plain,
    ( k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)) = k12_lattice3(sK0,sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1))
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f917,f903])).

fof(f917,plain,
    ( k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)) = k12_lattice3(sK0,k9_lattice3(sK0,sK4(k7_lattice3(sK0),sK1)),sK5(k7_lattice3(sK0),sK1))
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f898,f875])).

fof(f898,plain,
    ( k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)) = k12_lattice3(sK0,k9_lattice3(sK0,sK4(k7_lattice3(sK0),sK1)),k9_lattice3(sK0,sK5(k7_lattice3(sK0),sK1)))
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f73,f74,f775,f780,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
             => k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_7)).

fof(f864,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f139,f214,f216,f211,f203,f172,f163,f167,f175,f222,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r2_hidden(k13_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f791,plain,(
    spl6_26 ),
    inference(avatar_contradiction_clause,[],[f790])).

fof(f790,plain,
    ( $false
    | spl6_26 ),
    inference(subsumption_resolution,[],[f214,f755])).

fof(f755,plain,
    ( ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f753])).

fof(f753,plain,
    ( spl6_26
  <=> v3_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f789,plain,(
    spl6_27 ),
    inference(avatar_contradiction_clause,[],[f788])).

fof(f788,plain,
    ( $false
    | spl6_27 ),
    inference(subsumption_resolution,[],[f222,f759])).

fof(f759,plain,
    ( ~ v4_orders_2(k7_lattice3(sK0))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f757])).

fof(f757,plain,
    ( spl6_27
  <=> v4_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f787,plain,(
    spl6_28 ),
    inference(avatar_contradiction_clause,[],[f786])).

fof(f786,plain,
    ( $false
    | spl6_28 ),
    inference(subsumption_resolution,[],[f216,f763])).

fof(f763,plain,
    ( ~ v5_orders_2(k7_lattice3(sK0))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f761])).

fof(f761,plain,
    ( spl6_28
  <=> v5_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f785,plain,(
    spl6_29 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | spl6_29 ),
    inference(subsumption_resolution,[],[f211,f767])).

fof(f767,plain,
    ( ~ v1_lattice3(k7_lattice3(sK0))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f765])).

fof(f765,plain,
    ( spl6_29
  <=> v1_lattice3(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f783,plain,(
    spl6_30 ),
    inference(avatar_contradiction_clause,[],[f782])).

fof(f782,plain,
    ( $false
    | spl6_30 ),
    inference(subsumption_resolution,[],[f203,f771])).

fof(f771,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | spl6_30 ),
    inference(avatar_component_clause,[],[f769])).

fof(f769,plain,
    ( spl6_30
  <=> l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f781,plain,
    ( ~ spl6_26
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_30
    | spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_9
    | spl6_32
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f593,f166,f778,f174,f170,f162,f158,f769,f765,f761,f757,f753])).

fof(f158,plain,
    ( spl6_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f593,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | v2_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_7 ),
    inference(resolution,[],[f124,f167])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X1,X0)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_7(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f776,plain,
    ( ~ spl6_26
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_30
    | spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_9
    | spl6_31
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f608,f166,f773,f174,f170,f162,f158,f769,f765,f761,f757,f753])).

fof(f608,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | v2_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_7 ),
    inference(resolution,[],[f125,f167])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X1,X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_7(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f751,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f750])).

fof(f750,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f139,f160])).

fof(f160,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f158])).

fof(f747,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f746])).

fof(f746,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f679,f745])).

fof(f745,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f740,f652])).

fof(f652,plain,
    ( k13_lattice3(k7_lattice3(sK0),sK2(sK0,sK1),sK3(sK0,sK1)) = k12_lattice3(sK0,sK2(sK0,sK1),sK3(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f651,f526])).

fof(f526,plain,
    ( sK2(sK0,sK1) = k9_lattice3(sK0,sK2(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f74,f513,f105])).

fof(f513,plain,
    ( m1_subset_1(sK2(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f508,f509])).

fof(f509,plain,
    ( sK2(sK0,sK1) = k8_lattice3(sK0,sK2(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f74,f505,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k8_lattice3(X0,X1) = X1
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattice3)).

fof(f505,plain,
    ( m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f73,f74,f139,f152,f143,f147,f155,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v1_waybel_7(X1,X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f152,plain,
    ( ~ v1_waybel_7(sK1,sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f150])).

fof(f508,plain,
    ( m1_subset_1(k8_lattice3(sK0,sK2(sK0,sK1)),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f74,f505,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_lattice3)).

fof(f651,plain,
    ( k13_lattice3(k7_lattice3(sK0),sK2(sK0,sK1),sK3(sK0,sK1)) = k12_lattice3(sK0,k9_lattice3(sK0,sK2(sK0,sK1)),sK3(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f647,f558])).

fof(f558,plain,
    ( sK3(sK0,sK1) = k9_lattice3(sK0,sK3(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f74,f555,f105])).

fof(f555,plain,
    ( m1_subset_1(sK3(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f550,f551])).

fof(f551,plain,
    ( sK3(sK0,sK1) = k8_lattice3(sK0,sK3(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f74,f547,f104])).

fof(f547,plain,
    ( m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f73,f74,f139,f152,f143,f147,f155,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v1_waybel_7(X1,X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f550,plain,
    ( m1_subset_1(k8_lattice3(sK0,sK3(sK0,sK1)),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f74,f547,f137])).

fof(f647,plain,
    ( k12_lattice3(sK0,k9_lattice3(sK0,sK2(sK0,sK1)),k9_lattice3(sK0,sK3(sK0,sK1))) = k13_lattice3(k7_lattice3(sK0),sK2(sK0,sK1),sK3(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f73,f74,f513,f555,f116])).

fof(f740,plain,
    ( ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f139,f214,f222,f216,f211,f203,f163,f167,f171,f430,f513,f442,f555,f175,f123])).

fof(f123,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | r2_hidden(X4,X1)
      | r2_hidden(X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f442,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f73,f74,f139,f143,f147,f152,f155,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f430,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f73,f74,f139,f143,f147,f152,f155,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f171,plain,
    ( v2_waybel_7(sK1,k7_lattice3(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f679,plain,
    ( r2_hidden(k12_lattice3(sK0,sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f69,f70,f71,f73,f74,f139,f152,f143,f147,f155,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | r2_hidden(k12_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v1_waybel_7(X1,X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f400,plain,
    ( spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f74,f163,f156,f175,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v2_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f156,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f350,plain,
    ( spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f74,f148,f167,f175,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f148,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f146])).

fof(f334,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | spl6_1
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f74,f144,f163,f175,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v2_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | v1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f144,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f142])).

fof(f196,plain,
    ( spl6_1
    | spl6_6 ),
    inference(avatar_split_clause,[],[f81,f162,f142])).

fof(f81,plain,
    ( v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f193,plain,
    ( spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f84,f162,f154])).

fof(f84,plain,
    ( v2_waybel_0(sK1,k7_lattice3(sK0))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f190,plain,
    ( spl6_2
    | spl6_7 ),
    inference(avatar_split_clause,[],[f87,f166,f146])).

fof(f87,plain,
    ( v13_waybel_0(sK1,k7_lattice3(sK0))
    | v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f184,plain,
    ( spl6_3
    | spl6_8 ),
    inference(avatar_split_clause,[],[f93,f170,f150])).

fof(f93,plain,
    ( v2_waybel_7(sK1,k7_lattice3(sK0))
    | v1_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f181,plain,
    ( spl6_1
    | spl6_9 ),
    inference(avatar_split_clause,[],[f96,f174,f142])).

fof(f96,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f178,plain,
    ( spl6_4
    | spl6_9 ),
    inference(avatar_split_clause,[],[f99,f174,f154])).

fof(f99,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f177,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f140,f174,f170,f166,f162,f158,f154,f150,f146,f142])).

fof(f140,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

%------------------------------------------------------------------------------
