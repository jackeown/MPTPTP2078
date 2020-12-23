%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 229 expanded)
%              Number of leaves         :   21 (  83 expanded)
%              Depth                    :   15
%              Number of atoms          :  646 (1009 expanded)
%              Number of equality atoms :   34 (  70 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f127,f132,f143,f152,f188,f209,f219,f230])).

fof(f230,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f228,f126])).

fof(f126,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_6
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f228,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(resolution,[],[f227,f207])).

fof(f207,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl5_14
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f226,f110])).

fof(f110,plain,
    ( ! [X12,X11] :
        ( v6_orders_2(X12,sK0)
        | ~ m2_orders_2(X12,sK0,X11)
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f109,f56])).

fof(f56,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f109,plain,
    ( ! [X12,X11] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X12,sK0,X11)
        | v6_orders_2(X12,sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f108,f71])).

fof(f71,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f108,plain,
    ( ! [X12,X11] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X12,sK0,X11)
        | v6_orders_2(X12,sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f107,f66])).

fof(f66,plain,
    ( v4_orders_2(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f107,plain,
    ( ! [X12,X11] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X12,sK0,X11)
        | v6_orders_2(X12,sK0) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f83,f61])).

fof(f61,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f83,plain,
    ( ! [X12,X11] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X12,sK0,X11)
        | v6_orders_2(X12,sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f76,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | v6_orders_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f76,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f225,f56])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f224,f76])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f223,f71])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f222,f66])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl5_2
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f220,f61])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl5_15 ),
    inference(resolution,[],[f218,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v6_orders_2(k1_xboole_0,X0)
      | v2_struct_0(X0)
      | ~ m2_orders_2(k1_xboole_0,X0,X1) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).

fof(f218,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl5_15
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f219,plain,
    ( spl5_15
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f214,f205,f124,f74,f69,f64,f59,f54,f216])).

fof(f214,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f212,f126])).

fof(f212,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(resolution,[],[f207,f114])).

fof(f114,plain,
    ( ! [X14,X13] :
        ( ~ m2_orders_2(X14,sK0,X13)
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f113,f56])).

fof(f113,plain,
    ( ! [X14,X13] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X14,sK0,X13)
        | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f112,f71])).

fof(f112,plain,
    ( ! [X14,X13] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X14,sK0,X13)
        | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f111,f66])).

fof(f111,plain,
    ( ! [X14,X13] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X14,sK0,X13)
        | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f84,f61])).

fof(f84,plain,
    ( ! [X14,X13] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X14,sK0,X13)
        | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_5 ),
    inference(resolution,[],[f76,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f209,plain,
    ( spl5_14
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f200,f149,f136,f124,f74,f69,f64,f59,f54,f205])).

fof(f136,plain,
    ( spl5_8
  <=> k1_xboole_0 = k4_orders_2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f149,plain,
    ( spl5_10
  <=> k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f200,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f199,f151])).

fof(f151,plain,
    ( k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f199,plain,
    ( m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f197,f137])).

fof(f137,plain,
    ( k1_xboole_0 != k4_orders_2(sK0,sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f197,plain,
    ( m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1)
    | k1_xboole_0 = k4_orders_2(sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f144,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | m2_orders_2(X0,sK0,sK1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f118,f126])).

fof(f118,plain,
    ( ! [X15,X16] :
        ( ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X16,sK0,X15)
        | ~ r2_hidden(X16,k4_orders_2(sK0,X15)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f117,f56])).

fof(f117,plain,
    ( ! [X15,X16] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X16,sK0,X15)
        | ~ r2_hidden(X16,k4_orders_2(sK0,X15)) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f116,f71])).

fof(f116,plain,
    ( ! [X15,X16] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X16,sK0,X15)
        | ~ r2_hidden(X16,k4_orders_2(sK0,X15)) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f115,f66])).

fof(f115,plain,
    ( ! [X15,X16] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X16,sK0,X15)
        | ~ r2_hidden(X16,k4_orders_2(sK0,X15)) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f85,f61])).

fof(f85,plain,
    ( ! [X15,X16] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(X16,sK0,X15)
        | ~ r2_hidden(X16,k4_orders_2(sK0,X15)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f76,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,X2)
      | k4_orders_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

fof(f188,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f186,f56])).

fof(f186,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f185,f126])).

fof(f185,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f184,f76])).

fof(f184,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f183,f71])).

fof(f183,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f182,f66])).

fof(f182,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f181,f61])).

fof(f181,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f180,f31])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f180,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(superposition,[],[f47,f138])).

fof(f138,plain,
    ( k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f152,plain,
    ( spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f145,f140,f149])).

fof(f140,plain,
    ( spl5_9
  <=> r1_tarski(sK4(k4_orders_2(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f145,plain,
    ( k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))
    | ~ spl5_9 ),
    inference(resolution,[],[f142,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f142,plain,
    ( r1_tarski(sK4(k4_orders_2(sK0,sK1)),k1_xboole_0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f143,plain,
    ( spl5_8
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f134,f129,f140,f136])).

fof(f129,plain,
    ( spl5_7
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f134,plain,
    ( r1_tarski(sK4(k4_orders_2(sK0,sK1)),k1_xboole_0)
    | k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f133,f45])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | r1_tarski(X0,k1_xboole_0) )
    | ~ spl5_7 ),
    inference(superposition,[],[f46,f131])).

fof(f131,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f132,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f25,f129])).

fof(f25,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(f127,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f24,f124])).

fof(f24,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (2313)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.41  % (2313)Refutation not found, incomplete strategy% (2313)------------------------------
% 0.21/0.41  % (2313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (2313)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.41  
% 0.21/0.41  % (2313)Memory used [KB]: 1663
% 0.21/0.41  % (2313)Time elapsed: 0.003 s
% 0.21/0.41  % (2313)------------------------------
% 0.21/0.41  % (2313)------------------------------
% 0.21/0.44  % (2314)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (2301)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (2305)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (2307)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (2300)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (2300)Refutation not found, incomplete strategy% (2300)------------------------------
% 0.21/0.48  % (2300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2300)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2300)Memory used [KB]: 6268
% 0.21/0.48  % (2300)Time elapsed: 0.067 s
% 0.21/0.48  % (2300)------------------------------
% 0.21/0.48  % (2300)------------------------------
% 0.21/0.48  % (2312)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (2316)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (2312)Refutation not found, incomplete strategy% (2312)------------------------------
% 0.21/0.49  % (2312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2312)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2312)Memory used [KB]: 6140
% 0.21/0.49  % (2312)Time elapsed: 0.002 s
% 0.21/0.49  % (2312)------------------------------
% 0.21/0.49  % (2312)------------------------------
% 0.21/0.49  % (2306)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (2303)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (2304)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (2317)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (2301)Refutation not found, incomplete strategy% (2301)------------------------------
% 0.21/0.50  % (2301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (2301)Memory used [KB]: 10618
% 0.21/0.50  % (2301)Time elapsed: 0.067 s
% 0.21/0.50  % (2301)------------------------------
% 0.21/0.50  % (2301)------------------------------
% 0.21/0.50  % (2309)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (2303)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f127,f132,f143,f152,f188,f209,f219,f230])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_14 | ~spl5_15),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_14 | ~spl5_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f228,f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f124])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl5_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_15)),
% 0.21/0.50    inference(resolution,[],[f227,f207])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl5_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f205])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    spl5_14 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f226,f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X12,X11] : (v6_orders_2(X12,sK0) | ~m2_orders_2(X12,sK0,X11) | ~m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f109,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl5_1 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X12,X11] : (v2_struct_0(sK0) | ~m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X12,sK0,X11) | v6_orders_2(X12,sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f108,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    v5_orders_2(sK0) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl5_4 <=> v5_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ( ! [X12,X11] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X12,sK0,X11) | v6_orders_2(X12,sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f107,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    v4_orders_2(sK0) | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl5_3 <=> v4_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X12,X11] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X12,sK0,X11) | v6_orders_2(X12,sK0)) ) | (~spl5_2 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f83,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    v3_orders_2(sK0) | ~spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl5_2 <=> v3_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X12,X11] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X12,sK0,X11) | v6_orders_2(X12,sK0)) ) | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f76,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    l1_orders_2(sK0) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl5_5 <=> l1_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f225,f56])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f224,f76])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f223,f71])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f222,f66])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl5_2 | ~spl5_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f220,f61])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | ~spl5_15),
% 0.21/0.50    inference(resolution,[],[f218,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | v2_struct_0(X0) | ~m2_orders_2(k1_xboole_0,X0,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f216])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    spl5_15 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    spl5_15 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f214,f205,f124,f74,f69,f64,f59,f54,f216])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f212,f126])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14)),
% 0.21/0.50    inference(resolution,[],[f207,f114])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    ( ! [X14,X13] : (~m2_orders_2(X14,sK0,X13) | ~m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f113,f56])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ( ! [X14,X13] : (v2_struct_0(sK0) | ~m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X14,sK0,X13) | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f112,f71])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ( ! [X14,X13] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X14,sK0,X13) | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f111,f66])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ( ! [X14,X13] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X14,sK0,X13) | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f84,f61])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X14,X13] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X14,sK0,X13) | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f76,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    spl5_14 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_8 | ~spl5_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f200,f149,f136,f124,f74,f69,f64,f59,f54,f205])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl5_8 <=> k1_xboole_0 = k4_orders_2(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    spl5_10 <=> k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    m2_orders_2(k1_xboole_0,sK0,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_8 | ~spl5_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f199,f151])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) | ~spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f149])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f197,f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    k1_xboole_0 != k4_orders_2(sK0,sK1) | spl5_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) | k1_xboole_0 = k4_orders_2(sK0,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.50    inference(resolution,[],[f144,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | m2_orders_2(X0,sK0,sK1)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.50    inference(resolution,[],[f118,f126])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ( ! [X15,X16] : (~m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X16,sK0,X15) | ~r2_hidden(X16,k4_orders_2(sK0,X15))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f117,f56])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X15,X16] : (v2_struct_0(sK0) | ~m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X16,sK0,X15) | ~r2_hidden(X16,k4_orders_2(sK0,X15))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f116,f71])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ( ! [X15,X16] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X16,sK0,X15) | ~r2_hidden(X16,k4_orders_2(sK0,X15))) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f115,f66])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X15,X16] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X16,sK0,X15) | ~r2_hidden(X16,k4_orders_2(sK0,X15))) ) | (~spl5_2 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f85,f61])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X15,X16] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X16,sK0,X15) | ~r2_hidden(X16,k4_orders_2(sK0,X15))) ) | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f76,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f187])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f186,f56])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f185,f126])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f184,f76])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f183,f71])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f182,f66])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f181,f61])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl5_8),
% 0.21/0.50    inference(subsumption_resolution,[],[f180,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl5_8),
% 0.21/0.50    inference(superposition,[],[f47,f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    k1_xboole_0 = k4_orders_2(sK0,sK1) | ~spl5_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl5_10 | ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f145,f140,f149])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl5_9 <=> r1_tarski(sK4(k4_orders_2(sK0,sK1)),k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) | ~spl5_9),
% 0.21/0.50    inference(resolution,[],[f142,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    r1_tarski(sK4(k4_orders_2(sK0,sK1)),k1_xboole_0) | ~spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f140])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl5_8 | spl5_9 | ~spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f134,f129,f140,f136])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl5_7 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    r1_tarski(sK4(k4_orders_2(sK0,sK1)),k1_xboole_0) | k1_xboole_0 = k4_orders_2(sK0,sK1) | ~spl5_7),
% 0.21/0.50    inference(resolution,[],[f133,f45])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | r1_tarski(X0,k1_xboole_0)) ) | ~spl5_7),
% 0.21/0.50    inference(superposition,[],[f46,f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl5_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f129])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f129])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f124])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f74])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f69])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    v5_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f64])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    v4_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f59])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    v3_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ~spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f54])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (2303)------------------------------
% 0.21/0.50  % (2303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2303)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (2303)Memory used [KB]: 10746
% 0.21/0.50  % (2303)Time elapsed: 0.089 s
% 0.21/0.50  % (2303)------------------------------
% 0.21/0.50  % (2303)------------------------------
% 0.21/0.50  % (2299)Success in time 0.144 s
%------------------------------------------------------------------------------
