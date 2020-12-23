%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:28 EST 2020

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
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

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

% (18483)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (18467)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.44  % (18467)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f231,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f127,f132,f143,f152,f188,f209,f219,f230])).
% 0.21/0.44  fof(f230,plain,(
% 0.21/0.44    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_14 | ~spl5_15),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.44  fof(f229,plain,(
% 0.21/0.44    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_14 | ~spl5_15)),
% 0.21/0.44    inference(subsumption_resolution,[],[f228,f126])).
% 0.21/0.44  fof(f126,plain,(
% 0.21/0.44    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl5_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f124])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    spl5_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.44  fof(f228,plain,(
% 0.21/0.44    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_15)),
% 0.21/0.44    inference(resolution,[],[f227,f207])).
% 0.21/0.44  fof(f207,plain,(
% 0.21/0.44    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl5_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f205])).
% 0.21/0.44  fof(f205,plain,(
% 0.21/0.44    spl5_14 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.44  fof(f227,plain,(
% 0.21/0.44    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_15)),
% 0.21/0.44    inference(subsumption_resolution,[],[f226,f110])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    ( ! [X12,X11] : (v6_orders_2(X12,sK0) | ~m2_orders_2(X12,sK0,X11) | ~m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f109,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ~v2_struct_0(sK0) | spl5_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    spl5_1 <=> v2_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    ( ! [X12,X11] : (v2_struct_0(sK0) | ~m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X12,sK0,X11) | v6_orders_2(X12,sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f108,f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    v5_orders_2(sK0) | ~spl5_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl5_4 <=> v5_orders_2(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    ( ! [X12,X11] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X12,sK0,X11) | v6_orders_2(X12,sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f107,f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    v4_orders_2(sK0) | ~spl5_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f64])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl5_3 <=> v4_orders_2(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    ( ! [X12,X11] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X12,sK0,X11) | v6_orders_2(X12,sK0)) ) | (~spl5_2 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f83,f61])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    v3_orders_2(sK0) | ~spl5_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f59])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    spl5_2 <=> v3_orders_2(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ( ! [X12,X11] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X11,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X12,sK0,X11) | v6_orders_2(X12,sK0)) ) | ~spl5_5),
% 0.21/0.44    inference(resolution,[],[f76,f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    l1_orders_2(sK0) | ~spl5_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f74])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl5_5 <=> l1_orders_2(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.44  fof(f226,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_15)),
% 0.21/0.44    inference(subsumption_resolution,[],[f225,f56])).
% 0.21/0.44  fof(f225,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_15)),
% 0.21/0.44    inference(subsumption_resolution,[],[f224,f76])).
% 0.21/0.44  fof(f224,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_15)),
% 0.21/0.44    inference(subsumption_resolution,[],[f223,f71])).
% 0.21/0.44  fof(f223,plain,(
% 0.21/0.44    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_15)),
% 0.21/0.44    inference(subsumption_resolution,[],[f222,f66])).
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl5_2 | ~spl5_15)),
% 0.21/0.44    inference(subsumption_resolution,[],[f220,f61])).
% 0.21/0.44  fof(f220,plain,(
% 0.21/0.44    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v6_orders_2(k1_xboole_0,sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | ~spl5_15),
% 0.21/0.44    inference(resolution,[],[f218,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | v2_struct_0(X0) | ~m2_orders_2(k1_xboole_0,X0,X1)) )),
% 0.21/0.44    inference(equality_resolution,[],[f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).
% 0.21/0.44  fof(f218,plain,(
% 0.21/0.44    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f216])).
% 0.21/0.44  fof(f216,plain,(
% 0.21/0.44    spl5_15 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.44  fof(f219,plain,(
% 0.21/0.44    spl5_15 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f214,f205,f124,f74,f69,f64,f59,f54,f216])).
% 0.21/0.44  fof(f214,plain,(
% 0.21/0.44    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_14)),
% 0.21/0.44    inference(subsumption_resolution,[],[f212,f126])).
% 0.21/0.44  fof(f212,plain,(
% 0.21/0.44    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14)),
% 0.21/0.44    inference(resolution,[],[f207,f114])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    ( ! [X14,X13] : (~m2_orders_2(X14,sK0,X13) | ~m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f113,f56])).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    ( ! [X14,X13] : (v2_struct_0(sK0) | ~m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X14,sK0,X13) | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f112,f71])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    ( ! [X14,X13] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X14,sK0,X13) | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f111,f66])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    ( ! [X14,X13] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X14,sK0,X13) | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f84,f61])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    ( ! [X14,X13] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X13,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X14,sK0,X13) | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_5),
% 0.21/0.44    inference(resolution,[],[f76,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f209,plain,(
% 0.21/0.44    spl5_14 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_8 | ~spl5_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f200,f149,f136,f124,f74,f69,f64,f59,f54,f205])).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    spl5_8 <=> k1_xboole_0 = k4_orders_2(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    spl5_10 <=> k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.44  fof(f200,plain,(
% 0.21/0.44    m2_orders_2(k1_xboole_0,sK0,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_8 | ~spl5_10)),
% 0.21/0.44    inference(forward_demodulation,[],[f199,f151])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) | ~spl5_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f149])).
% 0.21/0.44  fof(f199,plain,(
% 0.21/0.44    m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_8)),
% 0.21/0.44    inference(subsumption_resolution,[],[f197,f137])).
% 0.21/0.44  fof(f137,plain,(
% 0.21/0.44    k1_xboole_0 != k4_orders_2(sK0,sK1) | spl5_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f136])).
% 0.21/0.44  fof(f197,plain,(
% 0.21/0.44    m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) | k1_xboole_0 = k4_orders_2(sK0,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.44    inference(resolution,[],[f144,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | m2_orders_2(X0,sK0,sK1)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.21/0.44    inference(resolution,[],[f118,f126])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    ( ! [X15,X16] : (~m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X16,sK0,X15) | ~r2_hidden(X16,k4_orders_2(sK0,X15))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f117,f56])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    ( ! [X15,X16] : (v2_struct_0(sK0) | ~m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X16,sK0,X15) | ~r2_hidden(X16,k4_orders_2(sK0,X15))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f116,f71])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    ( ! [X15,X16] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X16,sK0,X15) | ~r2_hidden(X16,k4_orders_2(sK0,X15))) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f115,f66])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    ( ! [X15,X16] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X16,sK0,X15) | ~r2_hidden(X16,k4_orders_2(sK0,X15))) ) | (~spl5_2 | ~spl5_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f85,f61])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    ( ! [X15,X16] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X15,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X16,sK0,X15) | ~r2_hidden(X16,k4_orders_2(sK0,X15))) ) | ~spl5_5),
% 0.21/0.44    inference(resolution,[],[f76,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.21/0.44    inference(equality_resolution,[],[f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  % (18483)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).
% 0.21/0.45  fof(f188,plain,(
% 0.21/0.45    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f187])).
% 0.21/0.45  fof(f187,plain,(
% 0.21/0.45    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8)),
% 0.21/0.45    inference(subsumption_resolution,[],[f186,f56])).
% 0.21/0.45  fof(f186,plain,(
% 0.21/0.45    v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8)),
% 0.21/0.45    inference(subsumption_resolution,[],[f185,f126])).
% 0.21/0.45  fof(f185,plain,(
% 0.21/0.45    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.21/0.45    inference(subsumption_resolution,[],[f184,f76])).
% 0.21/0.45  fof(f184,plain,(
% 0.21/0.45    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_8)),
% 0.21/0.45    inference(subsumption_resolution,[],[f183,f71])).
% 0.21/0.45  fof(f183,plain,(
% 0.21/0.45    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_8)),
% 0.21/0.45    inference(subsumption_resolution,[],[f182,f66])).
% 0.21/0.45  fof(f182,plain,(
% 0.21/0.45    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_8)),
% 0.21/0.45    inference(subsumption_resolution,[],[f181,f61])).
% 0.21/0.45  fof(f181,plain,(
% 0.21/0.45    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl5_8),
% 0.21/0.45    inference(subsumption_resolution,[],[f180,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    v1_xboole_0(k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.45  fof(f180,plain,(
% 0.21/0.45    ~v1_xboole_0(k1_xboole_0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl5_8),
% 0.21/0.45    inference(superposition,[],[f47,f138])).
% 0.21/0.45  fof(f138,plain,(
% 0.21/0.45    k1_xboole_0 = k4_orders_2(sK0,sK1) | ~spl5_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f136])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.21/0.45  fof(f152,plain,(
% 0.21/0.45    spl5_10 | ~spl5_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f145,f140,f149])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    spl5_9 <=> r1_tarski(sK4(k4_orders_2(sK0,sK1)),k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.45  fof(f145,plain,(
% 0.21/0.45    k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) | ~spl5_9),
% 0.21/0.45    inference(resolution,[],[f142,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    r1_tarski(sK4(k4_orders_2(sK0,sK1)),k1_xboole_0) | ~spl5_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f140])).
% 0.21/0.45  fof(f143,plain,(
% 0.21/0.45    spl5_8 | spl5_9 | ~spl5_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f134,f129,f140,f136])).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    spl5_7 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.45  fof(f134,plain,(
% 0.21/0.45    r1_tarski(sK4(k4_orders_2(sK0,sK1)),k1_xboole_0) | k1_xboole_0 = k4_orders_2(sK0,sK1) | ~spl5_7),
% 0.21/0.45    inference(resolution,[],[f133,f45])).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | r1_tarski(X0,k1_xboole_0)) ) | ~spl5_7),
% 0.21/0.45    inference(superposition,[],[f46,f131])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl5_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f129])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    spl5_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f129])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.21/0.45    inference(negated_conjecture,[],[f9])).
% 0.21/0.45  fof(f9,conjecture,(
% 0.21/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    spl5_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f124])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    spl5_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f30,f74])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    l1_orders_2(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl5_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f69])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    v5_orders_2(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl5_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f64])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    v4_orders_2(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    spl5_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f59])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    v3_orders_2(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ~spl5_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f54])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ~v2_struct_0(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (18467)------------------------------
% 0.21/0.45  % (18467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (18467)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (18467)Memory used [KB]: 10746
% 0.21/0.45  % (18467)Time elapsed: 0.061 s
% 0.21/0.45  % (18467)------------------------------
% 0.21/0.45  % (18467)------------------------------
% 0.21/0.45  % (18463)Success in time 0.094 s
%------------------------------------------------------------------------------
