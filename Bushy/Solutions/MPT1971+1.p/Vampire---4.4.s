%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t20_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:04 EDT 2019

% Result     : Theorem 3.19s
% Output     : Refutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  484 (2599 expanded)
%              Number of leaves         :   72 ( 774 expanded)
%              Depth                    :   33
%              Number of atoms          : 3072 (35603 expanded)
%              Number of equality atoms :   27 ( 258 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48017,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f317,f318,f320,f323,f324,f326,f327,f329,f332,f335,f441,f507,f512,f598,f601,f2977,f2985,f3007,f3015,f9028,f9054,f23273,f23285,f23625,f23639,f23653,f23667,f23681,f23686,f23693,f25361,f25382,f29100,f29109,f29120,f29166,f29287,f29310,f48013])).

fof(f48013,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | ~ spl11_1512
    | ~ spl11_2024
    | ~ spl11_2028 ),
    inference(avatar_contradiction_clause,[],[f48012])).

fof(f48012,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_1512
    | ~ spl11_2024
    | ~ spl11_2028 ),
    inference(subsumption_resolution,[],[f48011,f29198])).

fof(f29198,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_2024 ),
    inference(avatar_component_clause,[],[f29197])).

fof(f29197,plain,
    ( spl11_2024
  <=> m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2024])])).

fof(f48011,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_1512
    | ~ spl11_2028 ),
    inference(subsumption_resolution,[],[f48010,f29216])).

fof(f29216,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_2028 ),
    inference(avatar_component_clause,[],[f29215])).

fof(f29215,plain,
    ( spl11_2028
  <=> m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2028])])).

fof(f48010,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_1512 ),
    inference(subsumption_resolution,[],[f48009,f29238])).

fof(f29238,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29237,f151])).

fof(f151,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f122,f124,f123])).

fof(f123,plain,
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

fof(f124,plain,(
    ! [X0] :
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
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          | ~ v2_waybel_7(sK1,k7_lattice3(X0))
          | ~ v13_waybel_0(sK1,k7_lattice3(X0))
          | ~ v2_waybel_0(sK1,k7_lattice3(X0))
          | v1_xboole_0(sK1)
          | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_waybel_7(sK1,X0)
          | ~ v12_waybel_0(sK1,X0)
          | ~ v1_waybel_0(sK1,X0)
          | v1_xboole_0(sK1) )
        & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(sK1,k7_lattice3(X0))
            & v13_waybel_0(sK1,k7_lattice3(X0))
            & v2_waybel_0(sK1,k7_lattice3(X0))
            & ~ v1_xboole_0(sK1) )
          | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(sK1,X0)
            & v12_waybel_0(sK1,X0)
            & v1_waybel_0(sK1,X0)
            & ~ v1_xboole_0(sK1) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f122,plain,(
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
    inference(flattening,[],[f121])).

fof(f121,plain,(
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
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',t20_waybel_7)).

fof(f29237,plain,
    ( ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29236,f152])).

fof(f152,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f125])).

fof(f29236,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29235,f153])).

fof(f153,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f125])).

fof(f29235,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29234,f155])).

fof(f155,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f125])).

fof(f29234,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29233,f156])).

fof(f156,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f125])).

fof(f29233,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29232,f261])).

fof(f261,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f125])).

fof(f29232,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29231,f265])).

fof(f265,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl11_0
  <=> v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f29231,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29230,f271])).

fof(f271,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl11_2
  <=> v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f29230,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29181,f283])).

fof(f283,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl11_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f29181,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ spl11_5 ),
    inference(resolution,[],[f280,f2302])).

fof(f2302,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v12_waybel_0(X0,X1)
      | ~ v1_waybel_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ m1_subset_1(sK6(X1,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f2301])).

fof(f2301,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v12_waybel_0(X0,X1)
      | ~ v1_waybel_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK6(X1,X0),X0) ) ),
    inference(resolution,[],[f223,f238])).

fof(f238,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',t2_subset)).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
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
    inference(cnf_transformation,[],[f143])).

fof(f143,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK7(X0,X1),X1)
                & ~ r2_hidden(sK6(X0,X1),X1)
                & r2_hidden(k12_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f140,f142,f141])).

fof(f141,plain,(
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
            & ~ r2_hidden(sK6(X0,X1),X1)
            & r2_hidden(k12_lattice3(X0,sK6(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f142,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X2,X1)
          & r2_hidden(k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & ~ r2_hidden(X2,X1)
        & r2_hidden(k12_lattice3(X0,X2,sK7(X0,X1)),X1)
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f140,plain,(
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
    inference(rectify,[],[f139])).

fof(f139,plain,(
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
    inference(nnf_transformation,[],[f79])).

fof(f79,plain,(
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
    inference(flattening,[],[f78])).

fof(f78,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',d1_waybel_7)).

fof(f280,plain,
    ( ~ v1_waybel_7(sK1,sK0)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl11_5
  <=> ~ v1_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f48009,plain,
    ( m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_1512 ),
    inference(subsumption_resolution,[],[f47934,f29229])).

fof(f29229,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29228,f151])).

fof(f29228,plain,
    ( ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29227,f152])).

fof(f29227,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29226,f153])).

fof(f29226,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29225,f155])).

fof(f29225,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29224,f156])).

fof(f29224,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29223,f261])).

fof(f29223,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29222,f265])).

fof(f29222,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),sK1)
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29221,f271])).

fof(f29221,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),sK1)
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29180,f283])).

fof(f29180,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),sK1)
    | ~ spl11_5 ),
    inference(resolution,[],[f280,f2360])).

fof(f2360,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v12_waybel_0(X0,X1)
      | ~ v1_waybel_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ m1_subset_1(sK7(X1,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f2359])).

fof(f2359,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v12_waybel_0(X0,X1)
      | ~ v1_waybel_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK7(X1,X0),X0) ) ),
    inference(resolution,[],[f224,f238])).

fof(f224,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
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
    inference(cnf_transformation,[],[f143])).

fof(f47934,plain,
    ( m1_subset_1(sK7(sK0,sK1),sK1)
    | m1_subset_1(sK6(sK0,sK1),sK1)
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_1512 ),
    inference(resolution,[],[f47571,f29247])).

fof(f29247,plain,
    ( r2_hidden(k12_lattice3(sK0,sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29246,f151])).

fof(f29246,plain,
    ( r2_hidden(k12_lattice3(sK0,sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29245,f152])).

fof(f29245,plain,
    ( r2_hidden(k12_lattice3(sK0,sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29244,f153])).

fof(f29244,plain,
    ( r2_hidden(k12_lattice3(sK0,sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29243,f155])).

fof(f29243,plain,
    ( r2_hidden(k12_lattice3(sK0,sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29242,f156])).

fof(f29242,plain,
    ( r2_hidden(k12_lattice3(sK0,sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29241,f261])).

fof(f29241,plain,
    ( r2_hidden(k12_lattice3(sK0,sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29240,f265])).

fof(f29240,plain,
    ( r2_hidden(k12_lattice3(sK0,sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29239,f271])).

fof(f29239,plain,
    ( r2_hidden(k12_lattice3(sK0,sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f29182,f283])).

fof(f29182,plain,
    ( r2_hidden(k12_lattice3(sK0,sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_5 ),
    inference(resolution,[],[f280,f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | r2_hidden(k12_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f143])).

fof(f47571,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k12_lattice3(sK0,X4,X5),sK1)
        | m1_subset_1(X5,sK1)
        | m1_subset_1(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_1512 ),
    inference(subsumption_resolution,[],[f47525,f156])).

fof(f47525,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k12_lattice3(sK0,X4,X5),sK1)
        | m1_subset_1(X5,sK1)
        | m1_subset_1(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_1512 ),
    inference(resolution,[],[f43608,f456])).

fof(f456,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f455])).

fof(f455,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f243,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( k8_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',d6_lattice3)).

fof(f243,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',dt_k8_lattice3)).

fof(f43608,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(k7_lattice3(sK0)))
        | ~ r2_hidden(k12_lattice3(sK0,X5,X4),sK1)
        | m1_subset_1(X4,sK1)
        | m1_subset_1(X5,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_1512 ),
    inference(subsumption_resolution,[],[f43562,f156])).

fof(f43562,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(k7_lattice3(sK0)))
        | ~ r2_hidden(k12_lattice3(sK0,X5,X4),sK1)
        | m1_subset_1(X4,sK1)
        | m1_subset_1(X5,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_1512 ),
    inference(resolution,[],[f43492,f456])).

fof(f43492,plain,
    ( ! [X10,X11] :
        ( ~ m1_subset_1(X10,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X11,u1_struct_0(k7_lattice3(sK0)))
        | ~ r2_hidden(k12_lattice3(sK0,X10,X11),sK1)
        | m1_subset_1(X11,sK1)
        | m1_subset_1(X10,sK1) )
    | ~ spl11_1512 ),
    inference(resolution,[],[f43040,f237])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',t1_subset)).

fof(f43040,plain,
    ( ! [X10,X11] :
        ( r2_hidden(X10,sK1)
        | ~ m1_subset_1(X10,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X11,u1_struct_0(k7_lattice3(sK0)))
        | ~ r2_hidden(k12_lattice3(sK0,X10,X11),sK1)
        | m1_subset_1(X11,sK1) )
    | ~ spl11_1512 ),
    inference(resolution,[],[f31285,f237])).

fof(f31285,plain,
    ( ! [X12,X13] :
        ( r2_hidden(X13,sK1)
        | ~ r2_hidden(k12_lattice3(sK0,X12,X13),sK1)
        | ~ m1_subset_1(X12,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X13,u1_struct_0(k7_lattice3(sK0)))
        | r2_hidden(X12,sK1) )
    | ~ spl11_1512 ),
    inference(duplicate_literal_removal,[],[f31278])).

fof(f31278,plain,
    ( ! [X12,X13] :
        ( ~ r2_hidden(k12_lattice3(sK0,X12,X13),sK1)
        | r2_hidden(X13,sK1)
        | ~ m1_subset_1(X12,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X13,u1_struct_0(k7_lattice3(sK0)))
        | r2_hidden(X12,sK1)
        | ~ m1_subset_1(X12,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X13,u1_struct_0(k7_lattice3(sK0))) )
    | ~ spl11_1512 ),
    inference(superposition,[],[f23284,f4318])).

fof(f4318,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK0,X1,X0) = k13_lattice3(k7_lattice3(sK0),X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0))) ) ),
    inference(subsumption_resolution,[],[f4317,f156])).

fof(f4317,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK0,X1,X0) = k13_lattice3(k7_lattice3(sK0),X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f4307])).

fof(f4307,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK0,X1,X0) = k13_lattice3(k7_lattice3(sK0),X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(superposition,[],[f4302,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( k9_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
         => k9_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',d7_lattice3)).

fof(f4302,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK0,X0,k9_lattice3(sK0,X1)) = k13_lattice3(k7_lattice3(sK0),X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0))) ) ),
    inference(subsumption_resolution,[],[f4301,f156])).

fof(f4301,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK0,X0,k9_lattice3(sK0,X1)) = k13_lattice3(k7_lattice3(sK0),X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f4293])).

fof(f4293,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK0,X0,k9_lattice3(sK0,X1)) = k13_lattice3(k7_lattice3(sK0),X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(superposition,[],[f3653,f192])).

fof(f3653,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,X0)) = k13_lattice3(k7_lattice3(sK0),X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0))) ) ),
    inference(subsumption_resolution,[],[f3652,f151])).

fof(f3652,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
      | k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,X0)) = k13_lattice3(k7_lattice3(sK0),X1,X0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3651,f152])).

fof(f3651,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
      | k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,X0)) = k13_lattice3(k7_lattice3(sK0),X1,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3650,f153])).

fof(f3650,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
      | k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,X0)) = k13_lattice3(k7_lattice3(sK0),X1,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3646,f156])).

fof(f3646,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
      | ~ l1_orders_2(sK0)
      | k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,X0)) = k13_lattice3(k7_lattice3(sK0),X1,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f218,f155])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
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
    inference(flattening,[],[f76])).

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',t22_yellow_7)).

fof(f23284,plain,
    ( ! [X8,X7] :
        ( ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X8,X7),sK1)
        | r2_hidden(X7,sK1)
        | ~ m1_subset_1(X8,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X7,u1_struct_0(k7_lattice3(sK0)))
        | r2_hidden(X8,sK1) )
    | ~ spl11_1512 ),
    inference(avatar_component_clause,[],[f23283])).

fof(f23283,plain,
    ( spl11_1512
  <=> ! [X7,X8] :
        ( ~ m1_subset_1(X7,u1_struct_0(k7_lattice3(sK0)))
        | r2_hidden(X7,sK1)
        | ~ m1_subset_1(X8,u1_struct_0(k7_lattice3(sK0)))
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X8,X7),sK1)
        | r2_hidden(X8,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1512])])).

fof(f29310,plain,
    ( ~ spl11_958
    | spl11_2025 ),
    inference(avatar_contradiction_clause,[],[f29309])).

fof(f29309,plain,
    ( $false
    | ~ spl11_958
    | ~ spl11_2025 ),
    inference(subsumption_resolution,[],[f9008,f29269])).

fof(f29269,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl11_2025 ),
    inference(subsumption_resolution,[],[f29268,f156])).

fof(f29268,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl11_2025 ),
    inference(resolution,[],[f29201,f461])).

fof(f461,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f460])).

fof(f460,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f244,f192])).

fof(f244,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',dt_k9_lattice3)).

fof(f29201,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_2025 ),
    inference(avatar_component_clause,[],[f29200])).

fof(f29200,plain,
    ( spl11_2025
  <=> ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2025])])).

fof(f9008,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl11_958 ),
    inference(avatar_component_clause,[],[f9007])).

fof(f9007,plain,
    ( spl11_958
  <=> m1_subset_1(sK7(sK0,sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_958])])).

fof(f29287,plain,
    ( ~ spl11_954
    | spl11_2029 ),
    inference(avatar_contradiction_clause,[],[f29286])).

fof(f29286,plain,
    ( $false
    | ~ spl11_954
    | ~ spl11_2029 ),
    inference(subsumption_resolution,[],[f8995,f29273])).

fof(f29273,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl11_2029 ),
    inference(subsumption_resolution,[],[f29272,f156])).

fof(f29272,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl11_2029 ),
    inference(resolution,[],[f29219,f461])).

fof(f29219,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_2029 ),
    inference(avatar_component_clause,[],[f29218])).

fof(f29218,plain,
    ( spl11_2029
  <=> ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2029])])).

fof(f8995,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl11_954 ),
    inference(avatar_component_clause,[],[f8994])).

fof(f8994,plain,
    ( spl11_954
  <=> m1_subset_1(sK6(sK0,sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_954])])).

fof(f29166,plain,
    ( ~ spl11_1583
    | spl11_1780
    | ~ spl11_1580
    | ~ spl11_1584 ),
    inference(avatar_split_clause,[],[f25297,f23651,f23623,f25303,f23634])).

fof(f23634,plain,
    ( spl11_1583
  <=> ~ m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1583])])).

fof(f25303,plain,
    ( spl11_1780
  <=> r2_hidden(k12_lattice3(sK0,sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1780])])).

fof(f23623,plain,
    ( spl11_1580
  <=> r2_hidden(k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1580])])).

fof(f23651,plain,
    ( spl11_1584
  <=> m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1584])])).

fof(f25297,plain,
    ( r2_hidden(k12_lattice3(sK0,sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl11_1580
    | ~ spl11_1584 ),
    inference(subsumption_resolution,[],[f25260,f23652])).

fof(f23652,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl11_1584 ),
    inference(avatar_component_clause,[],[f23651])).

fof(f25260,plain,
    ( r2_hidden(k12_lattice3(sK0,sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl11_1580 ),
    inference(superposition,[],[f23624,f4318])).

fof(f23624,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ spl11_1580 ),
    inference(avatar_component_clause,[],[f23623])).

fof(f29120,plain,(
    ~ spl11_8 ),
    inference(avatar_contradiction_clause,[],[f29119])).

fof(f29119,plain,
    ( $false
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f292,f261])).

fof(f292,plain,
    ( v1_xboole_0(sK1)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl11_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f29109,plain,
    ( ~ spl11_15
    | spl11_1512
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(avatar_split_clause,[],[f29108,f2860,f2854,f2848,f2842,f427,f312,f300,f294,f23283,f309])).

fof(f309,plain,
    ( spl11_15
  <=> ~ v2_waybel_7(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f294,plain,
    ( spl11_10
  <=> v2_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f300,plain,
    ( spl11_12
  <=> v13_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f312,plain,
    ( spl11_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f427,plain,
    ( spl11_30
  <=> l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f2842,plain,
    ( spl11_404
  <=> v3_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_404])])).

fof(f2848,plain,
    ( spl11_406
  <=> v4_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_406])])).

fof(f2854,plain,
    ( spl11_408
  <=> v5_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_408])])).

fof(f2860,plain,
    ( spl11_410
  <=> v1_lattice3(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_410])])).

fof(f29108,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X2,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X3,sK1) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f29107,f3009])).

fof(f3009,plain,
    ( v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_404 ),
    inference(subsumption_resolution,[],[f3008,f156])).

fof(f3008,plain,
    ( v3_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_404 ),
    inference(superposition,[],[f2843,f400])).

fof(f400,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f398,f188])).

fof(f188,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',dt_k7_lattice3)).

fof(f398,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
      | ~ l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f190,f187])).

fof(f187,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f190,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',abstractness_v1_orders_2)).

fof(f2843,plain,
    ( v3_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))))
    | ~ spl11_404 ),
    inference(avatar_component_clause,[],[f2842])).

fof(f29107,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X2,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X3,sK1)
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f29106,f3017])).

fof(f3017,plain,
    ( v4_orders_2(k7_lattice3(sK0))
    | ~ spl11_406 ),
    inference(subsumption_resolution,[],[f3016,f156])).

fof(f3016,plain,
    ( v4_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_406 ),
    inference(superposition,[],[f2849,f400])).

fof(f2849,plain,
    ( v4_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))))
    | ~ spl11_406 ),
    inference(avatar_component_clause,[],[f2848])).

fof(f29106,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X2,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X3,sK1)
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f29105,f2979])).

fof(f2979,plain,
    ( v5_orders_2(k7_lattice3(sK0))
    | ~ spl11_408 ),
    inference(subsumption_resolution,[],[f2978,f156])).

fof(f2978,plain,
    ( v5_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_408 ),
    inference(superposition,[],[f2855,f400])).

fof(f2855,plain,
    ( v5_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))))
    | ~ spl11_408 ),
    inference(avatar_component_clause,[],[f2854])).

fof(f29105,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X2,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X3,sK1)
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f29104,f2992])).

fof(f2992,plain,
    ( v1_lattice3(k7_lattice3(sK0))
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f2987,f156])).

fof(f2987,plain,
    ( v1_lattice3(k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_410 ),
    inference(superposition,[],[f2861,f400])).

fof(f2861,plain,
    ( v1_lattice3(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))))
    | ~ spl11_410 ),
    inference(avatar_component_clause,[],[f2860])).

fof(f29104,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X2,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X3,sK1)
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f29103,f428])).

fof(f428,plain,
    ( l1_orders_2(k7_lattice3(sK0))
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f427])).

fof(f29103,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X2,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X3,sK1)
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f29102,f261])).

fof(f29102,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X2,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X3,sK1)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f29101,f295])).

fof(f295,plain,
    ( v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f294])).

fof(f29101,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X2,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X3,sK1)
        | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f23696,f313])).

fof(f313,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f312])).

fof(f23696,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X2,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
        | r2_hidden(X3,sK1)
        | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl11_12 ),
    inference(resolution,[],[f301,f211])).

fof(f211,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v13_waybel_0(X1,X0)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f138,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f135,f137,f136])).

fof(f136,plain,(
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

fof(f137,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X2,X1)
          & r2_hidden(k13_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & ~ r2_hidden(X2,X1)
        & r2_hidden(k13_lattice3(X0,X2,sK5(X0,X1)),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f135,plain,(
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
    inference(rectify,[],[f134])).

fof(f134,plain,(
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
    inference(nnf_transformation,[],[f73])).

fof(f73,plain,(
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
    inference(flattening,[],[f72])).

fof(f72,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',d2_waybel_7)).

fof(f301,plain,
    ( v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f300])).

fof(f29100,plain,
    ( ~ spl11_1510
    | spl11_1587
    | spl11_1589
    | ~ spl11_1774
    | ~ spl11_1776
    | ~ spl11_1780 ),
    inference(avatar_contradiction_clause,[],[f29099])).

fof(f29099,plain,
    ( $false
    | ~ spl11_1510
    | ~ spl11_1587
    | ~ spl11_1589
    | ~ spl11_1774
    | ~ spl11_1776
    | ~ spl11_1780 ),
    inference(subsumption_resolution,[],[f29098,f23666])).

fof(f23666,plain,
    ( ~ r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ spl11_1587 ),
    inference(avatar_component_clause,[],[f23665])).

fof(f23665,plain,
    ( spl11_1587
  <=> ~ r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1587])])).

fof(f29098,plain,
    ( r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ spl11_1510
    | ~ spl11_1589
    | ~ spl11_1774
    | ~ spl11_1776
    | ~ spl11_1780 ),
    inference(subsumption_resolution,[],[f29092,f25284])).

fof(f25284,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ spl11_1776 ),
    inference(avatar_component_clause,[],[f25283])).

fof(f25283,plain,
    ( spl11_1776
  <=> m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1776])])).

fof(f29092,plain,
    ( ~ m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ spl11_1510
    | ~ spl11_1589
    | ~ spl11_1774
    | ~ spl11_1780 ),
    inference(resolution,[],[f25304,f26216])).

fof(f26216,plain,
    ( ! [X24] :
        ( ~ r2_hidden(k12_lattice3(sK0,sK4(k7_lattice3(sK0),sK1),X24),sK1)
        | ~ m1_subset_1(X24,u1_struct_0(sK0))
        | r2_hidden(X24,sK1) )
    | ~ spl11_1510
    | ~ spl11_1589
    | ~ spl11_1774 ),
    inference(subsumption_resolution,[],[f26199,f25278])).

fof(f25278,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ spl11_1774 ),
    inference(avatar_component_clause,[],[f25277])).

fof(f25277,plain,
    ( spl11_1774
  <=> m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1774])])).

fof(f26199,plain,
    ( ! [X24] :
        ( r2_hidden(X24,sK1)
        | ~ m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X24,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,sK4(k7_lattice3(sK0),sK1),X24),sK1) )
    | ~ spl11_1510
    | ~ spl11_1589 ),
    inference(resolution,[],[f23272,f23680])).

fof(f23680,plain,
    ( ~ r2_hidden(sK4(k7_lattice3(sK0),sK1),sK1)
    | ~ spl11_1589 ),
    inference(avatar_component_clause,[],[f23679])).

fof(f23679,plain,
    ( spl11_1589
  <=> ~ r2_hidden(sK4(k7_lattice3(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1589])])).

fof(f23272,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,sK1)
        | r2_hidden(X8,sK1)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X7,X8),sK1) )
    | ~ spl11_1510 ),
    inference(avatar_component_clause,[],[f23271])).

fof(f23271,plain,
    ( spl11_1510
  <=> ! [X7,X8] :
        ( r2_hidden(X7,sK1)
        | r2_hidden(X8,sK1)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X7,X8),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1510])])).

fof(f25304,plain,
    ( r2_hidden(k12_lattice3(sK0,sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ spl11_1780 ),
    inference(avatar_component_clause,[],[f25303])).

fof(f25382,plain,
    ( ~ spl11_1582
    | spl11_1777 ),
    inference(avatar_contradiction_clause,[],[f25381])).

fof(f25381,plain,
    ( $false
    | ~ spl11_1582
    | ~ spl11_1777 ),
    inference(subsumption_resolution,[],[f25380,f156])).

fof(f25380,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_1582
    | ~ spl11_1777 ),
    inference(subsumption_resolution,[],[f25379,f23638])).

fof(f23638,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl11_1582 ),
    inference(avatar_component_clause,[],[f23637])).

fof(f23637,plain,
    ( spl11_1582
  <=> m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1582])])).

fof(f25379,plain,
    ( ~ m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl11_1777 ),
    inference(resolution,[],[f25287,f461])).

fof(f25287,plain,
    ( ~ m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ spl11_1777 ),
    inference(avatar_component_clause,[],[f25286])).

fof(f25286,plain,
    ( spl11_1777
  <=> ~ m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1777])])).

fof(f25361,plain,
    ( ~ spl11_1584
    | spl11_1775 ),
    inference(avatar_contradiction_clause,[],[f25360])).

fof(f25360,plain,
    ( $false
    | ~ spl11_1584
    | ~ spl11_1775 ),
    inference(subsumption_resolution,[],[f25359,f156])).

fof(f25359,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_1584
    | ~ spl11_1775 ),
    inference(subsumption_resolution,[],[f25358,f23652])).

fof(f25358,plain,
    ( ~ m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl11_1775 ),
    inference(resolution,[],[f25281,f461])).

fof(f25281,plain,
    ( ~ m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ spl11_1775 ),
    inference(avatar_component_clause,[],[f25280])).

fof(f25280,plain,
    ( spl11_1775
  <=> ~ m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1775])])).

fof(f23693,plain,
    ( ~ spl11_2
    | ~ spl11_6
    | spl11_13 ),
    inference(avatar_contradiction_clause,[],[f23692])).

fof(f23692,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f23691,f156])).

fof(f23691,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f23690,f271])).

fof(f23690,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl11_6
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f23689,f283])).

fof(f23689,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl11_13 ),
    inference(resolution,[],[f304,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f127,plain,(
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
    inference(flattening,[],[f126])).

fof(f126,plain,(
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
    inference(nnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',t28_yellow_7)).

fof(f304,plain,
    ( ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl11_13
  <=> ~ v13_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f23686,plain,
    ( ~ spl11_0
    | ~ spl11_6
    | spl11_11 ),
    inference(avatar_contradiction_clause,[],[f23685])).

fof(f23685,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f23684,f156])).

fof(f23684,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f23683,f265])).

fof(f23683,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f23682,f283])).

fof(f23682,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl11_11 ),
    inference(resolution,[],[f298,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f129,plain,(
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
    inference(flattening,[],[f128])).

fof(f128,plain,(
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
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',t26_yellow_7)).

fof(f298,plain,
    ( ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl11_11
  <=> ~ v2_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f23681,plain,
    ( ~ spl11_11
    | ~ spl11_13
    | ~ spl11_1589
    | spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(avatar_split_clause,[],[f23674,f2860,f2854,f2848,f2842,f427,f312,f309,f23679,f303,f297])).

fof(f23674,plain,
    ( ~ r2_hidden(sK4(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23673,f3009])).

fof(f23673,plain,
    ( ~ r2_hidden(sK4(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23672,f3017])).

fof(f23672,plain,
    ( ~ r2_hidden(sK4(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23671,f2979])).

fof(f23671,plain,
    ( ~ r2_hidden(sK4(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23670,f2992])).

fof(f23670,plain,
    ( ~ r2_hidden(sK4(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f23669,f428])).

fof(f23669,plain,
    ( ~ r2_hidden(sK4(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f23668,f261])).

fof(f23668,plain,
    ( ~ r2_hidden(sK4(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f23611,f313])).

fof(f23611,plain,
    ( ~ r2_hidden(sK4(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15 ),
    inference(resolution,[],[f310,f215])).

fof(f215,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f310,plain,
    ( ~ v2_waybel_7(sK1,k7_lattice3(sK0))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f309])).

fof(f23667,plain,
    ( ~ spl11_11
    | ~ spl11_13
    | ~ spl11_1587
    | spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(avatar_split_clause,[],[f23660,f2860,f2854,f2848,f2842,f427,f312,f309,f23665,f303,f297])).

fof(f23660,plain,
    ( ~ r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23659,f3009])).

fof(f23659,plain,
    ( ~ r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23658,f3017])).

fof(f23658,plain,
    ( ~ r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23657,f2979])).

fof(f23657,plain,
    ( ~ r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23656,f2992])).

fof(f23656,plain,
    ( ~ r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f23655,f428])).

fof(f23655,plain,
    ( ~ r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f23654,f261])).

fof(f23654,plain,
    ( ~ r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f23610,f313])).

fof(f23610,plain,
    ( ~ r2_hidden(sK5(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15 ),
    inference(resolution,[],[f310,f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f23653,plain,
    ( ~ spl11_11
    | ~ spl11_13
    | spl11_1584
    | spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(avatar_split_clause,[],[f23646,f2860,f2854,f2848,f2842,f427,f312,f309,f23651,f303,f297])).

fof(f23646,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23645,f3009])).

fof(f23645,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23644,f3017])).

fof(f23644,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23643,f2979])).

fof(f23643,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23642,f2992])).

fof(f23642,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f23641,f428])).

fof(f23641,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f23640,f261])).

fof(f23640,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f23609,f313])).

fof(f23609,plain,
    ( m1_subset_1(sK4(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15 ),
    inference(resolution,[],[f310,f212])).

fof(f212,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f23639,plain,
    ( ~ spl11_11
    | ~ spl11_13
    | spl11_1582
    | spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(avatar_split_clause,[],[f23632,f2860,f2854,f2848,f2842,f427,f312,f309,f23637,f303,f297])).

fof(f23632,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23631,f3009])).

fof(f23631,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23630,f3017])).

fof(f23630,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23629,f2979])).

fof(f23629,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23628,f2992])).

fof(f23628,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f23627,f428])).

fof(f23627,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f23626,f261])).

fof(f23626,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f23608,f313])).

fof(f23608,plain,
    ( m1_subset_1(sK5(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15 ),
    inference(resolution,[],[f310,f213])).

fof(f213,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f23625,plain,
    ( ~ spl11_11
    | ~ spl11_13
    | spl11_1580
    | spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(avatar_split_clause,[],[f23618,f2860,f2854,f2848,f2842,f427,f312,f309,f23623,f303,f297])).

fof(f23618,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23617,f3009])).

fof(f23617,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23616,f3017])).

fof(f23616,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23615,f2979])).

fof(f23615,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23614,f2992])).

fof(f23614,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f23613,f428])).

fof(f23613,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f23612,f261])).

fof(f23612,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f23607,f313])).

fof(f23607,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK4(k7_lattice3(sK0),sK1),sK5(k7_lattice3(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_15 ),
    inference(resolution,[],[f310,f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | r2_hidden(k13_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f23285,plain,
    ( ~ spl11_15
    | spl11_1512
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(avatar_split_clause,[],[f23281,f2860,f2854,f2848,f2842,f282,f270,f264,f23283,f309])).

fof(f23281,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X7,sK1)
        | r2_hidden(X8,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X8,X7),sK1) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23280,f265])).

fof(f23280,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X7,sK1)
        | r2_hidden(X8,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X8,X7),sK1)
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23279,f283])).

fof(f23279,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X7,sK1)
        | r2_hidden(X8,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X8,X7),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl11_2
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23278,f156])).

fof(f23278,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X7,sK1)
        | r2_hidden(X8,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X8,X7),sK1)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl11_2
    | ~ spl11_404
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23277,f3009])).

fof(f23277,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X7,sK1)
        | r2_hidden(X8,sK1)
        | ~ v3_orders_2(k7_lattice3(sK0))
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X8,X7),sK1)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl11_2
    | ~ spl11_406
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23276,f3017])).

fof(f23276,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X7,sK1)
        | r2_hidden(X8,sK1)
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0))
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X8,X7),sK1)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl11_2
    | ~ spl11_408
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23275,f2979])).

fof(f23275,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X7,sK1)
        | r2_hidden(X8,sK1)
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0))
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X8,X7),sK1)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl11_2
    | ~ spl11_410 ),
    inference(subsumption_resolution,[],[f23274,f2992])).

fof(f23274,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X7,sK1)
        | r2_hidden(X8,sK1)
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0))
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X8,X7),sK1)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f16994,f261])).

fof(f16994,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | r2_hidden(X7,sK1)
        | r2_hidden(X8,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0))
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X8,X7),sK1)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(sK1,sK0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f8000,f271])).

fof(f8000,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v12_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ v2_waybel_7(X3,k7_lattice3(X0))
      | r2_hidden(X2,X3)
      | r2_hidden(X1,X3)
      | v1_xboole_0(X3)
      | ~ v1_lattice3(k7_lattice3(X0))
      | ~ v5_orders_2(k7_lattice3(X0))
      | ~ v4_orders_2(k7_lattice3(X0))
      | ~ v3_orders_2(k7_lattice3(X0))
      | ~ r2_hidden(k13_lattice3(k7_lattice3(X0),X1,X2),X3)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X3,X0) ) ),
    inference(subsumption_resolution,[],[f7999,f198])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f7999,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k13_lattice3(k7_lattice3(X0),X1,X2),X3)
      | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ v2_waybel_7(X3,k7_lattice3(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | r2_hidden(X2,X3)
      | r2_hidden(X1,X3)
      | v1_xboole_0(X3)
      | ~ v1_lattice3(k7_lattice3(X0))
      | ~ v5_orders_2(k7_lattice3(X0))
      | ~ v4_orders_2(k7_lattice3(X0))
      | ~ v3_orders_2(k7_lattice3(X0))
      | ~ v12_waybel_0(X3,X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X3,X0) ) ),
    inference(duplicate_literal_removal,[],[f7995])).

fof(f7995,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k13_lattice3(k7_lattice3(X0),X1,X2),X3)
      | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ v2_waybel_7(X3,k7_lattice3(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | r2_hidden(X2,X3)
      | r2_hidden(X1,X3)
      | v1_xboole_0(X3)
      | ~ v1_lattice3(k7_lattice3(X0))
      | ~ v5_orders_2(k7_lattice3(X0))
      | ~ v4_orders_2(k7_lattice3(X0))
      | ~ v3_orders_2(k7_lattice3(X0))
      | ~ v12_waybel_0(X3,X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X3,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f4209,f197])).

fof(f4209,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_waybel_0(X1,k7_lattice3(X2))
      | ~ r2_hidden(k13_lattice3(k7_lattice3(X2),X0,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(X2)))
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(X2)))
      | ~ v2_waybel_7(X1,k7_lattice3(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
      | r2_hidden(X3,X1)
      | r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_lattice3(k7_lattice3(X2))
      | ~ v5_orders_2(k7_lattice3(X2))
      | ~ v4_orders_2(k7_lattice3(X2))
      | ~ v3_orders_2(k7_lattice3(X2))
      | ~ v12_waybel_0(X1,X2)
      | ~ l1_orders_2(X2) ) ),
    inference(subsumption_resolution,[],[f4208,f188])).

fof(f4208,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(k13_lattice3(k7_lattice3(X2),X0,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(X2)))
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(X2)))
      | ~ v2_waybel_7(X1,k7_lattice3(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
      | r2_hidden(X3,X1)
      | ~ v2_waybel_0(X1,k7_lattice3(X2))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(k7_lattice3(X2))
      | ~ v1_lattice3(k7_lattice3(X2))
      | ~ v5_orders_2(k7_lattice3(X2))
      | ~ v4_orders_2(k7_lattice3(X2))
      | ~ v3_orders_2(k7_lattice3(X2))
      | ~ v12_waybel_0(X1,X2)
      | ~ l1_orders_2(X2) ) ),
    inference(subsumption_resolution,[],[f4204,f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ v2_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f4204,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(k13_lattice3(k7_lattice3(X2),X0,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(k7_lattice3(X2)))
      | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(X2)))
      | ~ v2_waybel_7(X1,k7_lattice3(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X2))))
      | r2_hidden(X3,X1)
      | ~ v2_waybel_0(X1,k7_lattice3(X2))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(k7_lattice3(X2))
      | ~ v1_lattice3(k7_lattice3(X2))
      | ~ v5_orders_2(k7_lattice3(X2))
      | ~ v4_orders_2(k7_lattice3(X2))
      | ~ v3_orders_2(k7_lattice3(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v12_waybel_0(X1,X2)
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f211,f193])).

fof(f23273,plain,
    ( ~ spl11_5
    | spl11_1510
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f23269,f282,f270,f264,f23271,f279])).

fof(f23269,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,sK1)
        | ~ r2_hidden(k12_lattice3(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v1_waybel_7(sK1,sK0)
        | r2_hidden(X8,sK1) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f23268,f151])).

fof(f23268,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,sK1)
        | ~ r2_hidden(k12_lattice3(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v1_waybel_7(sK1,sK0)
        | r2_hidden(X8,sK1)
        | ~ v3_orders_2(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f23267,f152])).

fof(f23267,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,sK1)
        | ~ r2_hidden(k12_lattice3(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v1_waybel_7(sK1,sK0)
        | r2_hidden(X8,sK1)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f23266,f153])).

fof(f23266,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,sK1)
        | ~ r2_hidden(k12_lattice3(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v1_waybel_7(sK1,sK0)
        | r2_hidden(X8,sK1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f23265,f155])).

fof(f23265,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,sK1)
        | ~ r2_hidden(k12_lattice3(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v1_waybel_7(sK1,sK0)
        | r2_hidden(X8,sK1)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f23264,f156])).

fof(f23264,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,sK1)
        | ~ r2_hidden(k12_lattice3(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v1_waybel_7(sK1,sK0)
        | r2_hidden(X8,sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f23263,f261])).

fof(f23263,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,sK1)
        | ~ r2_hidden(k12_lattice3(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v1_waybel_7(sK1,sK0)
        | r2_hidden(X8,sK1)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f23262,f265])).

fof(f23262,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,sK1)
        | ~ r2_hidden(k12_lattice3(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v1_waybel_7(sK1,sK0)
        | r2_hidden(X8,sK1)
        | ~ v1_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f4394,f283])).

fof(f4394,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,sK1)
        | ~ r2_hidden(k12_lattice3(sK0,X7,X8),sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v1_waybel_7(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X8,sK1)
        | ~ v1_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f219,f271])).

fof(f219,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v12_waybel_0(X1,X0)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f143])).

fof(f9054,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | spl11_959 ),
    inference(avatar_contradiction_clause,[],[f9053])).

fof(f9053,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_959 ),
    inference(subsumption_resolution,[],[f9052,f156])).

fof(f9052,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_959 ),
    inference(subsumption_resolution,[],[f9050,f3383])).

fof(f3383,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3382,f151])).

fof(f3382,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3381,f152])).

fof(f3381,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3380,f153])).

fof(f3380,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3379,f155])).

fof(f3379,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3378,f156])).

fof(f3378,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3377,f261])).

fof(f3377,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3376,f265])).

fof(f3376,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3375,f271])).

fof(f3375,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3374,f283])).

fof(f3374,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_5 ),
    inference(resolution,[],[f221,f280])).

fof(f221,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f143])).

fof(f9050,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_959 ),
    inference(resolution,[],[f9011,f456])).

fof(f9011,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl11_959 ),
    inference(avatar_component_clause,[],[f9010])).

fof(f9010,plain,
    ( spl11_959
  <=> ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_959])])).

fof(f9028,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_5
    | ~ spl11_6
    | spl11_955 ),
    inference(avatar_contradiction_clause,[],[f9027])).

fof(f9027,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_955 ),
    inference(subsumption_resolution,[],[f9026,f156])).

fof(f9026,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_955 ),
    inference(subsumption_resolution,[],[f9024,f3049])).

fof(f3049,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3048,f151])).

fof(f3048,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3047,f152])).

fof(f3047,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3046,f153])).

fof(f3046,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3045,f155])).

fof(f3045,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3044,f156])).

fof(f3044,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3043,f261])).

fof(f3043,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3042,f265])).

fof(f3042,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_2
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3041,f271])).

fof(f3041,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f3040,f283])).

fof(f3040,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_5 ),
    inference(resolution,[],[f220,f280])).

fof(f220,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f143])).

fof(f9024,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_955 ),
    inference(resolution,[],[f8998,f456])).

fof(f8998,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl11_955 ),
    inference(avatar_component_clause,[],[f8997])).

fof(f8997,plain,
    ( spl11_955
  <=> ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_955])])).

fof(f3015,plain,(
    spl11_407 ),
    inference(avatar_contradiction_clause,[],[f3014])).

fof(f3014,plain,
    ( $false
    | ~ spl11_407 ),
    inference(subsumption_resolution,[],[f3013,f152])).

fof(f3013,plain,
    ( ~ v4_orders_2(sK0)
    | ~ spl11_407 ),
    inference(subsumption_resolution,[],[f3012,f156])).

fof(f3012,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ spl11_407 ),
    inference(resolution,[],[f3011,f226])).

fof(f226,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',fc2_yellow_7)).

fof(f3011,plain,
    ( ~ v4_orders_2(k7_lattice3(sK0))
    | ~ spl11_407 ),
    inference(subsumption_resolution,[],[f3010,f156])).

fof(f3010,plain,
    ( ~ v4_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_407 ),
    inference(superposition,[],[f2852,f400])).

fof(f2852,plain,
    ( ~ v4_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))))
    | ~ spl11_407 ),
    inference(avatar_component_clause,[],[f2851])).

fof(f2851,plain,
    ( spl11_407
  <=> ~ v4_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_407])])).

fof(f3007,plain,(
    spl11_405 ),
    inference(avatar_contradiction_clause,[],[f3006])).

fof(f3006,plain,
    ( $false
    | ~ spl11_405 ),
    inference(subsumption_resolution,[],[f3005,f151])).

fof(f3005,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl11_405 ),
    inference(subsumption_resolution,[],[f3004,f156])).

fof(f3004,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl11_405 ),
    inference(resolution,[],[f3003,f228])).

fof(f228,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',fc1_yellow_7)).

fof(f3003,plain,
    ( ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl11_405 ),
    inference(subsumption_resolution,[],[f3002,f156])).

fof(f3002,plain,
    ( ~ v3_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_405 ),
    inference(superposition,[],[f2846,f400])).

fof(f2846,plain,
    ( ~ v3_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))))
    | ~ spl11_405 ),
    inference(avatar_component_clause,[],[f2845])).

fof(f2845,plain,
    ( spl11_405
  <=> ~ v3_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_405])])).

fof(f2985,plain,(
    spl11_411 ),
    inference(avatar_contradiction_clause,[],[f2984])).

fof(f2984,plain,
    ( $false
    | ~ spl11_411 ),
    inference(subsumption_resolution,[],[f2983,f155])).

fof(f2983,plain,
    ( ~ v2_lattice3(sK0)
    | ~ spl11_411 ),
    inference(subsumption_resolution,[],[f2982,f156])).

fof(f2982,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ spl11_411 ),
    inference(resolution,[],[f2981,f232])).

fof(f232,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',fc5_yellow_7)).

fof(f2981,plain,
    ( ~ v1_lattice3(k7_lattice3(sK0))
    | ~ spl11_411 ),
    inference(subsumption_resolution,[],[f2980,f156])).

fof(f2980,plain,
    ( ~ v1_lattice3(k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_411 ),
    inference(superposition,[],[f2864,f400])).

fof(f2864,plain,
    ( ~ v1_lattice3(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))))
    | ~ spl11_411 ),
    inference(avatar_component_clause,[],[f2863])).

fof(f2863,plain,
    ( spl11_411
  <=> ~ v1_lattice3(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_411])])).

fof(f2977,plain,(
    spl11_409 ),
    inference(avatar_contradiction_clause,[],[f2976])).

fof(f2976,plain,
    ( $false
    | ~ spl11_409 ),
    inference(subsumption_resolution,[],[f2975,f153])).

fof(f2975,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl11_409 ),
    inference(subsumption_resolution,[],[f2974,f156])).

fof(f2974,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_409 ),
    inference(resolution,[],[f2973,f234])).

fof(f234,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t20_waybel_7.p',fc3_yellow_7)).

fof(f2973,plain,
    ( ~ v5_orders_2(k7_lattice3(sK0))
    | ~ spl11_409 ),
    inference(subsumption_resolution,[],[f2972,f156])).

fof(f2972,plain,
    ( ~ v5_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_409 ),
    inference(superposition,[],[f2858,f400])).

fof(f2858,plain,
    ( ~ v5_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))))
    | ~ spl11_409 ),
    inference(avatar_component_clause,[],[f2857])).

fof(f2857,plain,
    ( spl11_409
  <=> ~ v5_orders_2(g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_409])])).

fof(f601,plain,
    ( spl11_6
    | ~ spl11_17
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f600,f300,f315,f282])).

fof(f315,plain,
    ( spl11_17
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f600,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f599,f156])).

fof(f599,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl11_12 ),
    inference(resolution,[],[f301,f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f598,plain,
    ( spl11_16
    | ~ spl11_7
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f597,f270,f285,f312])).

fof(f285,plain,
    ( spl11_7
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f597,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f596,f156])).

fof(f596,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ l1_orders_2(sK0)
    | ~ spl11_2 ),
    inference(resolution,[],[f271,f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f512,plain,
    ( spl11_1
    | ~ spl11_10
    | ~ spl11_16 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f510,f156])).

fof(f510,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f509,f295])).

fof(f509,plain,
    ( ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_1
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f508,f313])).

fof(f508,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_1 ),
    inference(resolution,[],[f199,f268])).

fof(f268,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl11_1
  <=> ~ v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f199,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v2_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f507,plain,
    ( spl11_3
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f505,f156])).

fof(f505,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_3
    | ~ spl11_12
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f504,f301])).

fof(f504,plain,
    ( ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_3
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f503,f313])).

fof(f503,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_3 ),
    inference(resolution,[],[f195,f274])).

fof(f274,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl11_3
  <=> ~ v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f195,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f441,plain,(
    spl11_31 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl11_31 ),
    inference(subsumption_resolution,[],[f439,f156])).

fof(f439,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_31 ),
    inference(resolution,[],[f431,f188])).

fof(f431,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl11_31
  <=> ~ l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f335,plain,
    ( spl11_0
    | spl11_10 ),
    inference(avatar_split_clause,[],[f163,f294,f264])).

fof(f163,plain,
    ( v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f125])).

fof(f332,plain,
    ( spl11_6
    | spl11_10 ),
    inference(avatar_split_clause,[],[f166,f294,f282])).

fof(f166,plain,
    ( v2_waybel_0(sK1,k7_lattice3(sK0))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f125])).

fof(f329,plain,
    ( spl11_2
    | spl11_12 ),
    inference(avatar_split_clause,[],[f169,f300,f270])).

fof(f169,plain,
    ( v13_waybel_0(sK1,k7_lattice3(sK0))
    | v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f125])).

fof(f327,plain,
    ( spl11_6
    | spl11_12 ),
    inference(avatar_split_clause,[],[f171,f300,f282])).

fof(f171,plain,
    ( v13_waybel_0(sK1,k7_lattice3(sK0))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f125])).

fof(f326,plain,
    ( spl11_0
    | spl11_14 ),
    inference(avatar_split_clause,[],[f173,f306,f264])).

fof(f306,plain,
    ( spl11_14
  <=> v2_waybel_7(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f173,plain,
    ( v2_waybel_7(sK1,k7_lattice3(sK0))
    | v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f125])).

fof(f324,plain,
    ( spl11_4
    | spl11_14 ),
    inference(avatar_split_clause,[],[f175,f306,f276])).

fof(f276,plain,
    ( spl11_4
  <=> v1_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f175,plain,
    ( v2_waybel_7(sK1,k7_lattice3(sK0))
    | v1_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f125])).

fof(f323,plain,
    ( spl11_6
    | spl11_14 ),
    inference(avatar_split_clause,[],[f176,f306,f282])).

fof(f176,plain,
    ( v2_waybel_7(sK1,k7_lattice3(sK0))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f125])).

fof(f320,plain,
    ( spl11_2
    | spl11_16 ),
    inference(avatar_split_clause,[],[f179,f312,f270])).

fof(f179,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f125])).

fof(f318,plain,
    ( spl11_6
    | spl11_16 ),
    inference(avatar_split_clause,[],[f181,f312,f282])).

fof(f181,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f125])).

fof(f317,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | spl11_8
    | ~ spl11_11
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17 ),
    inference(avatar_split_clause,[],[f262,f315,f309,f303,f297,f291,f285,f279,f273,f267])).

fof(f262,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,
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
    inference(cnf_transformation,[],[f125])).
%------------------------------------------------------------------------------
