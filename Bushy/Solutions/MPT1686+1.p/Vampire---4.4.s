%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t66_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:01 EDT 2019

% Result     : Theorem 3.17s
% Output     : Refutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  778 (1944 expanded)
%              Number of leaves         :  127 ( 766 expanded)
%              Depth                    :   27
%              Number of atoms          : 4278 (8777 expanded)
%              Number of equality atoms :  242 ( 670 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29099,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f189,f196,f203,f210,f217,f256,f265,f275,f285,f311,f335,f365,f387,f408,f464,f468,f531,f575,f661,f765,f797,f808,f829,f840,f844,f854,f925,f932,f1402,f1534,f1900,f1931,f2276,f2303,f2325,f2346,f2456,f2489,f2627,f2635,f2694,f3229,f4668,f7467,f7500,f7551,f7576,f7719,f8041,f8073,f8153,f14932,f14989,f16927,f16966,f16996,f18002,f18009,f18027,f18036,f18045,f18058,f18092,f18110,f18158,f18177,f18204,f18217,f18235,f18311,f18343,f18377,f18384,f18425,f19018,f19041,f19042,f19286,f19396,f19482,f20042,f20834,f20840,f21520,f21522,f21785,f25093,f29014,f29098])).

fof(f29098,plain,
    ( ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | spl18_59
    | ~ spl18_66
    | ~ spl18_72
    | spl18_1499 ),
    inference(avatar_contradiction_clause,[],[f29097])).

fof(f29097,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_1499 ),
    inference(subsumption_resolution,[],[f29096,f761])).

fof(f761,plain,
    ( ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_59 ),
    inference(avatar_component_clause,[],[f760])).

fof(f760,plain,
    ( spl18_59
  <=> ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_59])])).

fof(f29096,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_1499 ),
    inference(subsumption_resolution,[],[f29095,f216])).

fof(f216,plain,
    ( l1_orders_2(sK0)
    | ~ spl18_8 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl18_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_8])])).

fof(f29095,plain,
    ( ~ l1_orders_2(sK0)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_1499 ),
    inference(subsumption_resolution,[],[f29094,f828])).

fof(f828,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl18_72 ),
    inference(avatar_component_clause,[],[f827])).

fof(f827,plain,
    ( spl18_72
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_72])])).

fof(f29094,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_1499 ),
    inference(subsumption_resolution,[],[f29093,f796])).

fof(f796,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl18_66 ),
    inference(avatar_component_clause,[],[f795])).

fof(f795,plain,
    ( spl18_66
  <=> v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_66])])).

fof(f29093,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_1499 ),
    inference(subsumption_resolution,[],[f29092,f202])).

fof(f202,plain,
    ( l1_orders_2(sK1)
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl18_4
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f29092,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_24
    | ~ spl18_1499 ),
    inference(resolution,[],[f29013,f348])).

fof(f348,plain,
    ( ! [X24,X25] :
        ( r1_orders_2(X25,sK7(X25,X24,k2_funct_1(sK2)),sK8(X25,X24,k2_funct_1(sK2)))
        | ~ l1_orders_2(X25)
        | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X25),u1_struct_0(X24))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X24))))
        | ~ l1_orders_2(X24)
        | v5_orders_3(k2_funct_1(sK2),X25,X24) )
    | ~ spl18_24 ),
    inference(resolution,[],[f334,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | r1_orders_2(X0,sK7(X0,X1,X2),sK8(X0,X1,X2))
      | v5_orders_3(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( ! [X6] :
                                ( r1_orders_2(X1,X5,X6)
                                | k1_funct_1(X2,X4) != X6
                                | k1_funct_1(X2,X3) != X5
                                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        | ~ r1_orders_2(X0,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( ! [X6] :
                                ( r1_orders_2(X1,X5,X6)
                                | k1_funct_1(X2,X4) != X6
                                | k1_funct_1(X2,X3) != X5
                                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        | ~ r1_orders_2(X0,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_orders_2(X0,X3,X4)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X1))
                                 => ( ( k1_funct_1(X2,X4) = X6
                                      & k1_funct_1(X2,X3) = X5 )
                                   => r1_orders_2(X1,X5,X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',d5_orders_3)).

fof(f334,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl18_24 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl18_24
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_24])])).

fof(f29013,plain,
    ( ~ r1_orders_2(sK1,sK7(sK1,sK0,k2_funct_1(sK2)),sK8(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl18_1499 ),
    inference(avatar_component_clause,[],[f29012])).

fof(f29012,plain,
    ( spl18_1499
  <=> ~ r1_orders_2(sK1,sK7(sK1,sK0,k2_funct_1(sK2)),sK8(sK1,sK0,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1499])])).

fof(f29014,plain,
    ( ~ spl18_1499
    | spl18_677
    | ~ spl18_1340 ),
    inference(avatar_split_clause,[],[f28819,f21790,f8151,f29012])).

fof(f8151,plain,
    ( spl18_677
  <=> ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),sK8(sK1,sK0,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_677])])).

fof(f21790,plain,
    ( spl18_1340
  <=> k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))) = sK7(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1340])])).

fof(f28819,plain,
    ( ~ r1_orders_2(sK1,sK7(sK1,sK0,k2_funct_1(sK2)),sK8(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl18_677
    | ~ spl18_1340 ),
    inference(superposition,[],[f8152,f21791])).

fof(f21791,plain,
    ( k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))) = sK7(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_1340 ),
    inference(avatar_component_clause,[],[f21790])).

fof(f8152,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),sK8(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl18_677 ),
    inference(avatar_component_clause,[],[f8151])).

fof(f25093,plain,
    ( spl18_1340
    | ~ spl18_1330
    | ~ spl18_1338 ),
    inference(avatar_split_clause,[],[f21798,f21783,f21518,f21790])).

fof(f21518,plain,
    ( spl18_1330
  <=> k1_funct_1(sK2,sK14(sK2,sK7(sK1,sK0,k2_funct_1(sK2)))) = sK7(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1330])])).

fof(f21783,plain,
    ( spl18_1338
  <=> sK9(sK1,sK0,k2_funct_1(sK2)) = sK14(sK2,sK7(sK1,sK0,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1338])])).

fof(f21798,plain,
    ( k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))) = sK7(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_1330
    | ~ spl18_1338 ),
    inference(superposition,[],[f21519,f21784])).

fof(f21784,plain,
    ( sK9(sK1,sK0,k2_funct_1(sK2)) = sK14(sK2,sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl18_1338 ),
    inference(avatar_component_clause,[],[f21783])).

fof(f21519,plain,
    ( k1_funct_1(sK2,sK14(sK2,sK7(sK1,sK0,k2_funct_1(sK2)))) = sK7(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_1330 ),
    inference(avatar_component_clause,[],[f21518])).

fof(f21785,plain,
    ( spl18_1338
    | ~ spl18_230
    | ~ spl18_240
    | ~ spl18_1310
    | ~ spl18_1330 ),
    inference(avatar_split_clause,[],[f21777,f21518,f20040,f2389,f2344,f21783])).

fof(f2344,plain,
    ( spl18_230
  <=> k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2))) = sK9(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_230])])).

fof(f2389,plain,
    ( spl18_240
  <=> r2_hidden(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_240])])).

fof(f20040,plain,
    ( spl18_1310
  <=> ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK1))
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK14(sK2,X2))) = sK14(sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1310])])).

fof(f21777,plain,
    ( sK9(sK1,sK0,k2_funct_1(sK2)) = sK14(sK2,sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl18_230
    | ~ spl18_240
    | ~ spl18_1310
    | ~ spl18_1330 ),
    inference(forward_demodulation,[],[f21776,f2345])).

fof(f2345,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2))) = sK9(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_230 ),
    inference(avatar_component_clause,[],[f2344])).

fof(f21776,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2))) = sK14(sK2,sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl18_240
    | ~ spl18_1310
    | ~ spl18_1330 ),
    inference(forward_demodulation,[],[f20843,f21519])).

fof(f20843,plain,
    ( k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK14(sK2,sK7(sK1,sK0,k2_funct_1(sK2))))) = sK14(sK2,sK7(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl18_240
    | ~ spl18_1310 ),
    inference(resolution,[],[f2390,f20041])).

fof(f20041,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK1))
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK14(sK2,X2))) = sK14(sK2,X2) )
    | ~ spl18_1310 ),
    inference(avatar_component_clause,[],[f20040])).

fof(f2390,plain,
    ( r2_hidden(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl18_240 ),
    inference(avatar_component_clause,[],[f2389])).

fof(f21522,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(theory_axiom,[])).

fof(f21520,plain,
    ( spl18_1330
    | ~ spl18_0
    | ~ spl18_18
    | ~ spl18_26
    | ~ spl18_240 ),
    inference(avatar_split_clause,[],[f20844,f2389,f360,f283,f187,f21518])).

fof(f187,plain,
    ( spl18_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_0])])).

fof(f283,plain,
    ( spl18_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_18])])).

fof(f360,plain,
    ( spl18_26
  <=> u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_26])])).

fof(f20844,plain,
    ( k1_funct_1(sK2,sK14(sK2,sK7(sK1,sK0,k2_funct_1(sK2)))) = sK7(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_0
    | ~ spl18_18
    | ~ spl18_26
    | ~ spl18_240 ),
    inference(resolution,[],[f2390,f19678])).

fof(f19678,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,u1_struct_0(sK1))
        | k1_funct_1(sK2,sK14(sK2,X4)) = X4 )
    | ~ spl18_0
    | ~ spl18_18
    | ~ spl18_26 ),
    inference(resolution,[],[f19571,f138])).

fof(f138,plain,(
    ! [X2,X0] :
      ( ~ sP13(X2,X0)
      | k1_funct_1(X0,sK14(X0,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',d5_funct_1)).

fof(f19571,plain,
    ( ! [X0] :
        ( sP13(X0,sK2)
        | ~ r2_hidden(X0,u1_struct_0(sK1)) )
    | ~ spl18_0
    | ~ spl18_18
    | ~ spl18_26 ),
    inference(superposition,[],[f303,f361])).

fof(f361,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl18_26 ),
    inference(avatar_component_clause,[],[f360])).

fof(f303,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK2))
        | sP13(X2,sK2) )
    | ~ spl18_0
    | ~ spl18_18 ),
    inference(subsumption_resolution,[],[f293,f188])).

fof(f188,plain,
    ( v1_funct_1(sK2)
    | ~ spl18_0 ),
    inference(avatar_component_clause,[],[f187])).

fof(f293,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK2)
        | sP13(X2,sK2)
        | ~ r2_hidden(X2,k2_relat_1(sK2)) )
    | ~ spl18_18 ),
    inference(resolution,[],[f284,f175])).

fof(f175,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP13(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP13(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f284,plain,
    ( v1_relat_1(sK2)
    | ~ spl18_18 ),
    inference(avatar_component_clause,[],[f283])).

fof(f20840,plain,
    ( ~ spl18_26
    | spl18_241
    | ~ spl18_1108
    | spl18_1297 ),
    inference(avatar_contradiction_clause,[],[f20839])).

fof(f20839,plain,
    ( $false
    | ~ spl18_26
    | ~ spl18_241
    | ~ spl18_1108
    | ~ spl18_1297 ),
    inference(subsumption_resolution,[],[f20128,f17133])).

fof(f17133,plain,
    ( m1_subset_1(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl18_1108 ),
    inference(avatar_component_clause,[],[f17132])).

fof(f17132,plain,
    ( spl18_1108
  <=> m1_subset_1(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1108])])).

fof(f20128,plain,
    ( ~ m1_subset_1(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl18_26
    | ~ spl18_241
    | ~ spl18_1297 ),
    inference(resolution,[],[f20112,f2393])).

fof(f2393,plain,
    ( ~ r2_hidden(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl18_241 ),
    inference(avatar_component_clause,[],[f2392])).

fof(f2392,plain,
    ( spl18_241
  <=> ~ r2_hidden(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_241])])).

fof(f20112,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl18_26
    | ~ spl18_1297 ),
    inference(forward_demodulation,[],[f20111,f361])).

fof(f20111,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl18_26
    | ~ spl18_1297 ),
    inference(forward_demodulation,[],[f19376,f361])).

fof(f19376,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_relat_1(sK2))
        | r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl18_1297 ),
    inference(resolution,[],[f19371,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',t2_subset)).

fof(f19371,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ spl18_1297 ),
    inference(avatar_component_clause,[],[f19370])).

fof(f19370,plain,
    ( spl18_1297
  <=> ~ v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1297])])).

fof(f20834,plain,
    ( ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | spl18_59
    | ~ spl18_66
    | ~ spl18_72
    | spl18_1109 ),
    inference(avatar_contradiction_clause,[],[f20833])).

fof(f20833,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_1109 ),
    inference(subsumption_resolution,[],[f19513,f761])).

fof(f19513,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_1109 ),
    inference(subsumption_resolution,[],[f19512,f202])).

fof(f19512,plain,
    ( ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_1109 ),
    inference(subsumption_resolution,[],[f19511,f828])).

fof(f19511,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_1109 ),
    inference(subsumption_resolution,[],[f19510,f796])).

fof(f19510,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_1109 ),
    inference(subsumption_resolution,[],[f19509,f334])).

fof(f19509,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_1109 ),
    inference(subsumption_resolution,[],[f17138,f216])).

fof(f17138,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_1109 ),
    inference(resolution,[],[f17136,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X0)
      | v5_orders_3(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f17136,plain,
    ( ~ m1_subset_1(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl18_1109 ),
    inference(avatar_component_clause,[],[f17135])).

fof(f17135,plain,
    ( spl18_1109
  <=> ~ m1_subset_1(sK7(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1109])])).

fof(f20042,plain,
    ( spl18_1310
    | spl18_112
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_18
    | ~ spl18_26
    | ~ spl18_34 ),
    inference(avatar_split_clause,[],[f19686,f406,f360,f283,f254,f187,f1225,f20040])).

fof(f1225,plain,
    ( spl18_112
  <=> ! [X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3)))
        | k1_xboole_0 = X3
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_112])])).

fof(f254,plain,
    ( spl18_12
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_12])])).

fof(f406,plain,
    ( spl18_34
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_34])])).

fof(f19686,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),X3)
        | ~ r2_hidden(X2,u1_struct_0(sK1))
        | k1_xboole_0 = X3
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK14(sK2,X2))) = sK14(sK2,X2) )
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_18
    | ~ spl18_26
    | ~ spl18_34 ),
    inference(forward_demodulation,[],[f19685,f407])).

fof(f407,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl18_34 ),
    inference(avatar_component_clause,[],[f406])).

fof(f19685,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),X3)
        | ~ r2_hidden(X2,u1_struct_0(sK1))
        | k1_xboole_0 = X3
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK14(sK2,X2))) = sK14(sK2,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X3))) )
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_18
    | ~ spl18_26
    | ~ spl18_34 ),
    inference(forward_demodulation,[],[f19677,f407])).

fof(f19677,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,u1_struct_0(sK1))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),X3)
        | k1_xboole_0 = X3
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK14(sK2,X2))) = sK14(sK2,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X3))) )
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_18
    | ~ spl18_26 ),
    inference(resolution,[],[f19571,f598])).

fof(f598,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP13(X2,X0)
        | ~ v1_funct_2(sK2,k1_relat_1(X0),X1)
        | k1_xboole_0 = X1
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK14(X0,X2))) = sK14(X0,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) )
    | ~ spl18_0
    | ~ spl18_12 ),
    inference(resolution,[],[f596,f137])).

fof(f137,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK14(X0,X2),k1_relat_1(X0))
      | ~ sP13(X2,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f596,plain,
    ( ! [X37,X38,X36] :
        ( ~ r2_hidden(X38,X36)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
        | ~ v1_funct_2(sK2,X36,X37)
        | k1_xboole_0 = X37
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X38)) = X38 )
    | ~ spl18_0
    | ~ spl18_12 ),
    inference(subsumption_resolution,[],[f235,f255])).

fof(f255,plain,
    ( v2_funct_1(sK2)
    | ~ spl18_12 ),
    inference(avatar_component_clause,[],[f254])).

fof(f235,plain,
    ( ! [X37,X38,X36] :
        ( ~ v1_funct_2(sK2,X36,X37)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
        | ~ v2_funct_1(sK2)
        | ~ r2_hidden(X38,X36)
        | k1_xboole_0 = X37
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X38)) = X38 )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f169])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',t32_funct_2)).

fof(f19482,plain,
    ( ~ spl18_72
    | spl18_77
    | ~ spl18_142 ),
    inference(avatar_contradiction_clause,[],[f19481])).

fof(f19481,plain,
    ( $false
    | ~ spl18_72
    | ~ spl18_77
    | ~ spl18_142 ),
    inference(subsumption_resolution,[],[f19273,f857])).

fof(f857,plain,
    ( u1_struct_0(sK1) != k1_relat_1(k2_funct_1(sK2))
    | ~ spl18_77 ),
    inference(avatar_component_clause,[],[f856])).

fof(f856,plain,
    ( spl18_77
  <=> u1_struct_0(sK1) != k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_77])])).

fof(f19273,plain,
    ( u1_struct_0(sK1) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl18_72
    | ~ spl18_142 ),
    inference(subsumption_resolution,[],[f1537,f828])).

fof(f1537,plain,
    ( u1_struct_0(sK1) = k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl18_142 ),
    inference(superposition,[],[f152,f1527])).

fof(f1527,plain,
    ( u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl18_142 ),
    inference(avatar_component_clause,[],[f1526])).

fof(f1526,plain,
    ( spl18_142
  <=> u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_142])])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',redefinition_k1_relset_1)).

fof(f19396,plain,
    ( spl18_3
    | ~ spl18_36
    | ~ spl18_88 ),
    inference(avatar_contradiction_clause,[],[f19395])).

fof(f19395,plain,
    ( $false
    | ~ spl18_3
    | ~ spl18_36
    | ~ spl18_88 ),
    inference(subsumption_resolution,[],[f19394,f195])).

fof(f195,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl18_3 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl18_3
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).

fof(f19394,plain,
    ( v2_struct_0(sK1)
    | ~ spl18_36
    | ~ spl18_88 ),
    inference(subsumption_resolution,[],[f19390,f460])).

fof(f460,plain,
    ( l1_struct_0(sK1)
    | ~ spl18_36 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl18_36
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_36])])).

fof(f19390,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl18_88 ),
    inference(resolution,[],[f1023,f131])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',fc2_struct_0)).

fof(f1023,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl18_88 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f1022,plain,
    ( spl18_88
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_88])])).

fof(f19286,plain,
    ( ~ spl18_70
    | spl18_89
    | ~ spl18_1180
    | spl18_1217 ),
    inference(avatar_contradiction_clause,[],[f19285])).

fof(f19285,plain,
    ( $false
    | ~ spl18_70
    | ~ spl18_89
    | ~ spl18_1180
    | ~ spl18_1217 ),
    inference(subsumption_resolution,[],[f19284,f18035])).

fof(f18035,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl18_1180 ),
    inference(avatar_component_clause,[],[f18034])).

fof(f18034,plain,
    ( spl18_1180
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1180])])).

fof(f19284,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl18_70
    | ~ spl18_89
    | ~ spl18_1217 ),
    inference(resolution,[],[f18323,f1036])).

fof(f1036,plain,
    ( ! [X4] :
        ( r2_hidden(k1_funct_1(sK2,X4),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl18_70
    | ~ spl18_89 ),
    inference(resolution,[],[f1028,f807])).

fof(f807,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_70 ),
    inference(avatar_component_clause,[],[f806])).

fof(f806,plain,
    ( spl18_70
  <=> ! [X0] :
        ( m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_70])])).

fof(f1028,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(X0,u1_struct_0(sK1)) )
    | ~ spl18_89 ),
    inference(resolution,[],[f1026,f146])).

fof(f1026,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl18_89 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f1025,plain,
    ( spl18_89
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_89])])).

fof(f18323,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3),u1_struct_0(sK1))
    | ~ spl18_1217 ),
    inference(avatar_component_clause,[],[f18322])).

fof(f18322,plain,
    ( spl18_1217
  <=> ~ r2_hidden(k1_funct_1(sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1217])])).

fof(f19042,plain,
    ( u1_struct_0(sK1) != k1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(theory_axiom,[])).

fof(f19041,plain,
    ( ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | spl18_69
    | ~ spl18_1178
    | ~ spl18_1190
    | spl18_1201 ),
    inference(avatar_contradiction_clause,[],[f19040])).

fof(f19040,plain,
    ( $false
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_1178
    | ~ spl18_1190
    | ~ spl18_1201 ),
    inference(subsumption_resolution,[],[f18215,f18157])).

fof(f18157,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ spl18_1201 ),
    inference(avatar_component_clause,[],[f18156])).

fof(f18156,plain,
    ( spl18_1201
  <=> ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1201])])).

fof(f18215,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_1178
    | ~ spl18_1190 ),
    inference(subsumption_resolution,[],[f18214,f801])).

fof(f801,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_69 ),
    inference(avatar_component_clause,[],[f800])).

fof(f800,plain,
    ( spl18_69
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_69])])).

fof(f18214,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_1178
    | ~ spl18_1190 ),
    inference(subsumption_resolution,[],[f18213,f18026])).

fof(f18026,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl18_1178 ),
    inference(avatar_component_clause,[],[f18025])).

fof(f18025,plain,
    ( spl18_1178
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1178])])).

fof(f18213,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_1190 ),
    inference(subsumption_resolution,[],[f18212,f274])).

fof(f274,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl18_16 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl18_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_16])])).

fof(f18212,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_1190 ),
    inference(subsumption_resolution,[],[f18211,f264])).

fof(f264,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl18_14 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl18_14
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_14])])).

fof(f18211,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_1190 ),
    inference(superposition,[],[f18091,f234])).

fof(f234,plain,
    ( ! [X35,X33,X34] :
        ( k3_funct_2(X33,X34,sK2,X35) = k1_funct_1(sK2,X35)
        | ~ v1_funct_2(sK2,X33,X34)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ m1_subset_1(X35,X33)
        | v1_xboole_0(X33) )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f168])).

fof(f168,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',redefinition_k3_funct_2)).

fof(f18091,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ spl18_1190 ),
    inference(avatar_component_clause,[],[f18090])).

fof(f18090,plain,
    ( spl18_1190
  <=> r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1190])])).

fof(f19018,plain,
    ( ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_58
    | ~ spl18_66
    | ~ spl18_72
    | spl18_89
    | spl18_1185
    | ~ spl18_1200
    | ~ spl18_1218
    | ~ spl18_1220
    | ~ spl18_1222
    | ~ spl18_1226 ),
    inference(avatar_contradiction_clause,[],[f19017])).

fof(f19017,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_58
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89
    | ~ spl18_1185
    | ~ spl18_1200
    | ~ spl18_1218
    | ~ spl18_1220
    | ~ spl18_1222
    | ~ spl18_1226 ),
    inference(subsumption_resolution,[],[f19016,f18048])).

fof(f18048,plain,
    ( ~ r1_orders_2(sK0,sK3,sK4)
    | ~ spl18_1185 ),
    inference(avatar_component_clause,[],[f18047])).

fof(f18047,plain,
    ( spl18_1185
  <=> ~ r1_orders_2(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1185])])).

fof(f19016,plain,
    ( r1_orders_2(sK0,sK3,sK4)
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_58
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89
    | ~ spl18_1200
    | ~ spl18_1218
    | ~ spl18_1220
    | ~ spl18_1222
    | ~ spl18_1226 ),
    inference(forward_demodulation,[],[f19015,f18383])).

fof(f18383,plain,
    ( k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)) = sK3
    | ~ spl18_1222 ),
    inference(avatar_component_clause,[],[f18382])).

fof(f18382,plain,
    ( spl18_1222
  <=> k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1222])])).

fof(f19015,plain,
    ( r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)),sK4)
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_58
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89
    | ~ spl18_1200
    | ~ spl18_1218
    | ~ spl18_1220
    | ~ spl18_1226 ),
    inference(forward_demodulation,[],[f19014,f18342])).

fof(f18342,plain,
    ( k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)) = sK4
    | ~ spl18_1218 ),
    inference(avatar_component_clause,[],[f18341])).

fof(f18341,plain,
    ( spl18_1218
  <=> k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1218])])).

fof(f19014,plain,
    ( r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)),k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)))
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_58
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89
    | ~ spl18_1200
    | ~ spl18_1220
    | ~ spl18_1226 ),
    inference(subsumption_resolution,[],[f19013,f18424])).

fof(f18424,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3),u1_struct_0(sK1))
    | ~ spl18_1226 ),
    inference(avatar_component_clause,[],[f18423])).

fof(f18423,plain,
    ( spl18_1226
  <=> m1_subset_1(k1_funct_1(sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1226])])).

fof(f19013,plain,
    ( ~ m1_subset_1(k1_funct_1(sK2,sK3),u1_struct_0(sK1))
    | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)),k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)))
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_58
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89
    | ~ spl18_1200
    | ~ spl18_1220 ),
    inference(subsumption_resolution,[],[f18997,f18376])).

fof(f18376,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK4),u1_struct_0(sK1))
    | ~ spl18_1220 ),
    inference(avatar_component_clause,[],[f18375])).

fof(f18375,plain,
    ( spl18_1220
  <=> m1_subset_1(k1_funct_1(sK2,sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1220])])).

fof(f18997,plain,
    ( ~ m1_subset_1(k1_funct_1(sK2,sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK2,sK3),u1_struct_0(sK1))
    | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)),k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)))
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_58
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89
    | ~ spl18_1200 ),
    inference(resolution,[],[f18995,f18154])).

fof(f18154,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ spl18_1200 ),
    inference(avatar_component_clause,[],[f18153])).

fof(f18153,plain,
    ( spl18_1200
  <=> r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1200])])).

fof(f18995,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),X0),k1_funct_1(k2_funct_1(sK2),X1)) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_58
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89 ),
    inference(subsumption_resolution,[],[f16810,f764])).

fof(f764,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_58 ),
    inference(avatar_component_clause,[],[f763])).

fof(f763,plain,
    ( spl18_58
  <=> v5_orders_3(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_58])])).

fof(f16810,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X0,X1)
        | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),X0),k1_funct_1(k2_funct_1(sK2),X1))
        | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89 ),
    inference(subsumption_resolution,[],[f16809,f7509])).

fof(f7509,plain,
    ( ! [X7] :
        ( m1_subset_1(k1_funct_1(k2_funct_1(sK2),X7),u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89 ),
    inference(subsumption_resolution,[],[f7508,f1026])).

fof(f7508,plain,
    ( ! [X7] :
        ( m1_subset_1(k1_funct_1(k2_funct_1(sK2),X7),u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f7504,f828])).

fof(f7504,plain,
    ( ! [X7] :
        ( m1_subset_1(k1_funct_1(k2_funct_1(sK2),X7),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X7,u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl18_24
    | ~ spl18_66 ),
    inference(resolution,[],[f796,f1032])).

fof(f1032,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
        | m1_subset_1(k1_funct_1(k2_funct_1(sK2),X2),X1)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(X0) )
    | ~ spl18_24 ),
    inference(duplicate_literal_removal,[],[f1031])).

fof(f1031,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_funct_1(k2_funct_1(sK2),X2),X1)
        | ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(X0)
        | ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(X0) )
    | ~ spl18_24 ),
    inference(superposition,[],[f352,f353])).

fof(f353,plain,
    ( ! [X37,X35,X36] :
        ( k3_funct_2(X35,X36,k2_funct_1(sK2),X37) = k1_funct_1(k2_funct_1(sK2),X37)
        | ~ v1_funct_2(k2_funct_1(sK2),X35,X36)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ m1_subset_1(X37,X35)
        | v1_xboole_0(X35) )
    | ~ spl18_24 ),
    inference(resolution,[],[f334,f168])).

fof(f352,plain,
    ( ! [X33,X34,X32] :
        ( m1_subset_1(k3_funct_2(X32,X33,k2_funct_1(sK2),X34),X33)
        | ~ v1_funct_2(k2_funct_1(sK2),X32,X33)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ m1_subset_1(X34,X32)
        | v1_xboole_0(X32) )
    | ~ spl18_24 ),
    inference(resolution,[],[f334,f167])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',dt_k3_funct_2)).

fof(f16809,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),X0),k1_funct_1(k2_funct_1(sK2),X1))
        | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89 ),
    inference(subsumption_resolution,[],[f16808,f202])).

fof(f16808,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),X0),k1_funct_1(k2_funct_1(sK2),X1))
        | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0) )
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89 ),
    inference(subsumption_resolution,[],[f7691,f828])).

fof(f7691,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),X0),k1_funct_1(k2_funct_1(sK2),X1))
        | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0) )
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89 ),
    inference(duplicate_literal_removal,[],[f7688])).

fof(f7688,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),X0),k1_funct_1(k2_funct_1(sK2),X1))
        | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0) )
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89 ),
    inference(resolution,[],[f7546,f796])).

fof(f7546,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_orders_2(X1,X0,X2)
        | ~ l1_orders_2(X1)
        | ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),X2),u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),X0),k1_funct_1(k2_funct_1(sK2),X2))
        | ~ v5_orders_3(k2_funct_1(sK2),X1,sK0) )
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89 ),
    inference(subsumption_resolution,[],[f7545,f334])).

fof(f7545,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_orders_2(X1,X0,X2)
        | ~ l1_orders_2(X1)
        | ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),X2),u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),X0),k1_funct_1(k2_funct_1(sK2),X2))
        | ~ v5_orders_3(k2_funct_1(sK2),X1,sK0) )
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89 ),
    inference(subsumption_resolution,[],[f7510,f216])).

fof(f7510,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_orders_2(X1,X0,X2)
        | ~ l1_orders_2(X1)
        | ~ m1_subset_1(k1_funct_1(k2_funct_1(sK2),X2),u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_funct_1(k2_funct_1(sK2),X0),k1_funct_1(k2_funct_1(sK2),X2))
        | ~ v5_orders_3(k2_funct_1(sK2),X1,sK0) )
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_89 ),
    inference(resolution,[],[f7509,f174])).

fof(f174,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k1_funct_1(X2,X3),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X4)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_funct_1(X2,X4),u1_struct_0(X1))
      | r1_orders_2(X1,k1_funct_1(X2,X3),k1_funct_1(X2,X4))
      | ~ v5_orders_3(X2,X0,X1) ) ),
    inference(equality_resolution,[],[f173])).

fof(f173,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X4)
      | ~ m1_subset_1(k1_funct_1(X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | k1_funct_1(X2,X4) != X6
      | r1_orders_2(X1,k1_funct_1(X2,X3),X6)
      | ~ v5_orders_3(X2,X0,X1) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | k1_funct_1(X2,X3) != X5
      | k1_funct_1(X2,X4) != X6
      | r1_orders_2(X1,X5,X6)
      | ~ v5_orders_3(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f18425,plain,
    ( spl18_1226
    | ~ spl18_1216 ),
    inference(avatar_split_clause,[],[f18335,f18325,f18423])).

fof(f18325,plain,
    ( spl18_1216
  <=> r2_hidden(k1_funct_1(sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1216])])).

fof(f18335,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3),u1_struct_0(sK1))
    | ~ spl18_1216 ),
    inference(resolution,[],[f18326,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',t1_subset)).

fof(f18326,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),u1_struct_0(sK1))
    | ~ spl18_1216 ),
    inference(avatar_component_clause,[],[f18325])).

fof(f18384,plain,
    ( spl18_1222
    | spl18_112
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_1192 ),
    inference(avatar_split_clause,[],[f18119,f18108,f254,f187,f1225,f18382])).

fof(f18108,plain,
    ( spl18_1192
  <=> r2_hidden(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1192])])).

fof(f18119,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),X0)
        | k1_xboole_0 = X0
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK3)) = sK3 )
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_1192 ),
    inference(resolution,[],[f18109,f596])).

fof(f18109,plain,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | ~ spl18_1192 ),
    inference(avatar_component_clause,[],[f18108])).

fof(f18377,plain,
    ( spl18_1220
    | ~ spl18_1214 ),
    inference(avatar_split_clause,[],[f18319,f18309,f18375])).

fof(f18309,plain,
    ( spl18_1214
  <=> r2_hidden(k1_funct_1(sK2,sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1214])])).

fof(f18319,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK4),u1_struct_0(sK1))
    | ~ spl18_1214 ),
    inference(resolution,[],[f18310,f145])).

fof(f18310,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4),u1_struct_0(sK1))
    | ~ spl18_1214 ),
    inference(avatar_component_clause,[],[f18309])).

fof(f18343,plain,
    ( spl18_1218
    | spl18_112
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_1182 ),
    inference(avatar_split_clause,[],[f18072,f18043,f254,f187,f1225,f18341])).

fof(f18043,plain,
    ( spl18_1182
  <=> r2_hidden(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1182])])).

fof(f18072,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),X0)
        | k1_xboole_0 = X0
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK4)) = sK4 )
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_1182 ),
    inference(resolution,[],[f18044,f596])).

fof(f18044,plain,
    ( r2_hidden(sK4,u1_struct_0(sK0))
    | ~ spl18_1182 ),
    inference(avatar_component_clause,[],[f18043])).

fof(f18311,plain,
    ( spl18_1214
    | ~ spl18_0
    | ~ spl18_18
    | ~ spl18_26
    | ~ spl18_34
    | ~ spl18_1182 ),
    inference(avatar_split_clause,[],[f18078,f18043,f406,f360,f283,f187,f18309])).

fof(f18078,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4),u1_struct_0(sK1))
    | ~ spl18_0
    | ~ spl18_18
    | ~ spl18_26
    | ~ spl18_34
    | ~ spl18_1182 ),
    inference(forward_demodulation,[],[f18070,f361])).

fof(f18070,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4),k2_relat_1(sK2))
    | ~ spl18_0
    | ~ spl18_18
    | ~ spl18_34
    | ~ spl18_1182 ),
    inference(resolution,[],[f18044,f545])).

fof(f545,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) )
    | ~ spl18_0
    | ~ spl18_18
    | ~ spl18_34 ),
    inference(forward_demodulation,[],[f544,f407])).

fof(f544,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl18_0
    | ~ spl18_18 ),
    inference(resolution,[],[f304,f177])).

fof(f177,plain,(
    ! [X0,X3] :
      ( sP13(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP13(X2,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f304,plain,
    ( ! [X3] :
        ( ~ sP13(X3,sK2)
        | r2_hidden(X3,k2_relat_1(sK2)) )
    | ~ spl18_0
    | ~ spl18_18 ),
    inference(subsumption_resolution,[],[f294,f188])).

fof(f294,plain,
    ( ! [X3] :
        ( ~ v1_funct_1(sK2)
        | ~ sP13(X3,sK2)
        | r2_hidden(X3,k2_relat_1(sK2)) )
    | ~ spl18_18 ),
    inference(resolution,[],[f284,f176])).

fof(f176,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP13(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP13(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f18235,plain,
    ( ~ spl18_10
    | ~ spl18_12
    | ~ spl18_20
    | ~ spl18_1184
    | ~ spl18_1186 ),
    inference(avatar_contradiction_clause,[],[f18234])).

fof(f18234,plain,
    ( $false
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_20
    | ~ spl18_1184
    | ~ spl18_1186 ),
    inference(subsumption_resolution,[],[f18218,f18057])).

fof(f18057,plain,
    ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ spl18_1186 ),
    inference(avatar_component_clause,[],[f18056])).

fof(f18056,plain,
    ( spl18_1186
  <=> r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1186])])).

fof(f18218,plain,
    ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_20
    | ~ spl18_1184 ),
    inference(subsumption_resolution,[],[f18093,f18051])).

fof(f18051,plain,
    ( r1_orders_2(sK0,sK3,sK4)
    | ~ spl18_1184 ),
    inference(avatar_component_clause,[],[f18050])).

fof(f18050,plain,
    ( spl18_1184
  <=> r1_orders_2(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1184])])).

fof(f18093,plain,
    ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ r1_orders_2(sK0,sK3,sK4)
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f18017,f249])).

fof(f249,plain,
    ( v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_10 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl18_10
  <=> v23_waybel_0(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_10])])).

fof(f18017,plain,
    ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ r1_orders_2(sK0,sK3,sK4)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_12
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f830,f310])).

fof(f310,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl18_20 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl18_20
  <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_20])])).

fof(f830,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ r1_orders_2(sK0,sK3,sK4)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_12 ),
    inference(subsumption_resolution,[],[f88,f255])).

fof(f88,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ r1_orders_2(sK0,sK3,sK4)
    | ~ v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v23_waybel_0(X2,X0,X1)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v23_waybel_0(X2,X0,X1)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( r1_orders_2(X0,X3,X4)
                            <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) ) ) )
                    & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & v2_funct_1(X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) ) ) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',t66_waybel_0)).

fof(f18217,plain,
    ( ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | spl18_69
    | ~ spl18_1180
    | spl18_1187
    | ~ spl18_1190 ),
    inference(avatar_contradiction_clause,[],[f18216])).

fof(f18216,plain,
    ( $false
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_1180
    | ~ spl18_1187
    | ~ spl18_1190 ),
    inference(subsumption_resolution,[],[f18099,f18091])).

fof(f18099,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_1180
    | ~ spl18_1187 ),
    inference(subsumption_resolution,[],[f18098,f801])).

fof(f18098,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_1180
    | ~ spl18_1187 ),
    inference(subsumption_resolution,[],[f18097,f18035])).

fof(f18097,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_1187 ),
    inference(subsumption_resolution,[],[f18096,f274])).

fof(f18096,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_1187 ),
    inference(subsumption_resolution,[],[f18094,f264])).

fof(f18094,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_1187 ),
    inference(superposition,[],[f18054,f234])).

fof(f18054,plain,
    ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ spl18_1187 ),
    inference(avatar_component_clause,[],[f18053])).

fof(f18053,plain,
    ( spl18_1187
  <=> ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1187])])).

fof(f18204,plain,
    ( ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_70
    | ~ spl18_128
    | ~ spl18_1178
    | ~ spl18_1180
    | ~ spl18_1184
    | spl18_1201 ),
    inference(avatar_contradiction_clause,[],[f18203])).

fof(f18203,plain,
    ( $false
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_70
    | ~ spl18_128
    | ~ spl18_1178
    | ~ spl18_1180
    | ~ spl18_1184
    | ~ spl18_1201 ),
    inference(subsumption_resolution,[],[f18202,f18157])).

fof(f18202,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_70
    | ~ spl18_128
    | ~ spl18_1178
    | ~ spl18_1180
    | ~ spl18_1184 ),
    inference(subsumption_resolution,[],[f18201,f18035])).

fof(f18201,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_70
    | ~ spl18_128
    | ~ spl18_1178
    | ~ spl18_1184 ),
    inference(subsumption_resolution,[],[f18192,f18026])).

fof(f18192,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_70
    | ~ spl18_128
    | ~ spl18_1184 ),
    inference(resolution,[],[f18181,f18051])).

fof(f18181,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,k1_funct_1(sK2,X0),k1_funct_1(sK2,X1)) )
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_70
    | ~ spl18_128 ),
    inference(subsumption_resolution,[],[f18180,f1398])).

fof(f1398,plain,
    ( v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_128 ),
    inference(avatar_component_clause,[],[f1397])).

fof(f1397,plain,
    ( spl18_128
  <=> v5_orders_3(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_128])])).

fof(f18180,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r1_orders_2(sK1,k1_funct_1(sK2,X0),k1_funct_1(sK2,X1))
        | ~ v5_orders_3(sK2,sK0,sK1) )
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_70 ),
    inference(subsumption_resolution,[],[f18179,f807])).

fof(f18179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(k1_funct_1(sK2,X1),u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_funct_1(sK2,X0),k1_funct_1(sK2,X1))
        | ~ v5_orders_3(sK2,sK0,sK1) )
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_70 ),
    inference(subsumption_resolution,[],[f18178,f216])).

fof(f18178,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(k1_funct_1(sK2,X1),u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_funct_1(sK2,X0),k1_funct_1(sK2,X1))
        | ~ v5_orders_3(sK2,sK0,sK1) )
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_70 ),
    inference(subsumption_resolution,[],[f1836,f264])).

fof(f1836,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(k1_funct_1(sK2,X1),u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_funct_1(sK2,X0),k1_funct_1(sK2,X1))
        | ~ v5_orders_3(sK2,sK0,sK1) )
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_70 ),
    inference(duplicate_literal_removal,[],[f1834])).

fof(f1834,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(k1_funct_1(sK2,X1),u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_funct_1(sK2,X0),k1_funct_1(sK2,X1))
        | ~ v5_orders_3(sK2,sK0,sK1) )
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_70 ),
    inference(resolution,[],[f953,f274])).

fof(f953,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_orders_2(X1,X0,X2)
        | ~ l1_orders_2(X1)
        | ~ m1_subset_1(k1_funct_1(sK2,X2),u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_funct_1(sK2,X0),k1_funct_1(sK2,X2))
        | ~ v5_orders_3(sK2,X1,sK1) )
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_70 ),
    inference(subsumption_resolution,[],[f952,f188])).

fof(f952,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_orders_2(X1,X0,X2)
        | ~ l1_orders_2(X1)
        | ~ m1_subset_1(k1_funct_1(sK2,X2),u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_funct_1(sK2,X0),k1_funct_1(sK2,X2))
        | ~ v5_orders_3(sK2,X1,sK1) )
    | ~ spl18_4
    | ~ spl18_70 ),
    inference(subsumption_resolution,[],[f951,f202])).

fof(f951,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ r1_orders_2(X1,X0,X2)
        | ~ l1_orders_2(X1)
        | ~ m1_subset_1(k1_funct_1(sK2,X2),u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_funct_1(sK2,X0),k1_funct_1(sK2,X2))
        | ~ v5_orders_3(sK2,X1,sK1) )
    | ~ spl18_70 ),
    inference(resolution,[],[f807,f174])).

fof(f18177,plain,
    ( ~ spl18_0
    | spl18_3
    | ~ spl18_4
    | spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_14
    | ~ spl18_16
    | spl18_129 ),
    inference(avatar_contradiction_clause,[],[f18176])).

fof(f18176,plain,
    ( $false
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f18015,f249])).

fof(f18015,plain,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f18014,f202])).

fof(f18014,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f18013,f195])).

fof(f18013,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f18012,f209])).

fof(f209,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl18_7 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl18_7
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).

fof(f18012,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f18011,f274])).

fof(f18011,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f18010,f264])).

fof(f18010,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f16919,f216])).

fof(f16919,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_129 ),
    inference(resolution,[],[f1401,f221])).

fof(f221,plain,
    ( ! [X6,X7] :
        ( v5_orders_3(sK2,X7,X6)
        | ~ l1_orders_2(X7)
        | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(X6))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X6))))
        | v2_struct_0(X7)
        | v2_struct_0(X6)
        | ~ l1_orders_2(X6)
        | ~ v23_waybel_0(sK2,X7,X6) )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v5_orders_3(X2,X0,X1)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( ~ ( ~ v2_struct_0(X1)
                      & ~ v2_struct_0(X0) )
                 => ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) ) )
                & ~ ( ~ ( v23_waybel_0(X2,X0,X1)
                      <=> ( ? [X3] :
                              ( v5_orders_3(X3,X1,X0)
                              & k2_funct_1(X2) = X3
                              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                              & v1_funct_1(X3) )
                          & v5_orders_3(X2,X0,X1)
                          & v2_funct_1(X2) ) )
                    & ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',d38_waybel_0)).

fof(f1401,plain,
    ( ~ v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_129 ),
    inference(avatar_component_clause,[],[f1400])).

fof(f1400,plain,
    ( spl18_129
  <=> ~ v5_orders_3(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_129])])).

fof(f18158,plain,
    ( ~ spl18_1201
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | spl18_69
    | ~ spl18_1178
    | spl18_1191 ),
    inference(avatar_split_clause,[],[f18115,f18087,f18025,f800,f273,f263,f187,f18156])).

fof(f18087,plain,
    ( spl18_1191
  <=> ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1191])])).

fof(f18115,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_1178
    | ~ spl18_1191 ),
    inference(subsumption_resolution,[],[f18114,f801])).

fof(f18114,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_1178
    | ~ spl18_1191 ),
    inference(subsumption_resolution,[],[f18113,f18026])).

fof(f18113,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_1191 ),
    inference(subsumption_resolution,[],[f18112,f274])).

fof(f18112,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_1191 ),
    inference(subsumption_resolution,[],[f18111,f264])).

fof(f18111,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_1191 ),
    inference(superposition,[],[f18088,f234])).

fof(f18088,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ spl18_1191 ),
    inference(avatar_component_clause,[],[f18087])).

fof(f18110,plain,
    ( spl18_1192
    | spl18_69
    | ~ spl18_1180 ),
    inference(avatar_split_clause,[],[f18037,f18034,f800,f18108])).

fof(f18037,plain,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | ~ spl18_69
    | ~ spl18_1180 ),
    inference(resolution,[],[f18035,f863])).

fof(f863,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl18_69 ),
    inference(resolution,[],[f801,f146])).

fof(f18092,plain,
    ( spl18_1190
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | spl18_69
    | ~ spl18_1180
    | ~ spl18_1186 ),
    inference(avatar_split_clause,[],[f18064,f18056,f18034,f800,f273,f263,f187,f18090])).

fof(f18064,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_1180
    | ~ spl18_1186 ),
    inference(subsumption_resolution,[],[f18063,f801])).

fof(f18063,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_1180
    | ~ spl18_1186 ),
    inference(subsumption_resolution,[],[f18062,f18035])).

fof(f18062,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_1186 ),
    inference(subsumption_resolution,[],[f18061,f274])).

fof(f18061,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_1186 ),
    inference(subsumption_resolution,[],[f18059,f264])).

fof(f18059,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_1186 ),
    inference(superposition,[],[f18057,f234])).

fof(f18058,plain,
    ( spl18_1184
    | spl18_1186
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_20 ),
    inference(avatar_split_clause,[],[f18038,f309,f254,f248,f18056,f18050])).

fof(f18038,plain,
    ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | r1_orders_2(sK0,sK3,sK4)
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f18016,f249])).

fof(f18016,plain,
    ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | r1_orders_2(sK0,sK3,sK4)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_12
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f831,f310])).

fof(f831,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | r1_orders_2(sK0,sK3,sK4)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_12 ),
    inference(subsumption_resolution,[],[f87,f255])).

fof(f87,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4))
    | r1_orders_2(sK0,sK3,sK4)
    | ~ v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f18045,plain,
    ( spl18_1182
    | spl18_69
    | ~ spl18_1178 ),
    inference(avatar_split_clause,[],[f18028,f18025,f800,f18043])).

fof(f18028,plain,
    ( r2_hidden(sK4,u1_struct_0(sK0))
    | ~ spl18_69
    | ~ spl18_1178 ),
    inference(resolution,[],[f18026,f863])).

fof(f18036,plain,
    ( spl18_1180
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_20 ),
    inference(avatar_split_clause,[],[f18029,f309,f254,f248,f18034])).

fof(f18029,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f18019,f249])).

fof(f18019,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_12
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f832,f310])).

fof(f832,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_12 ),
    inference(subsumption_resolution,[],[f90,f255])).

fof(f90,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f18027,plain,
    ( spl18_1178
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_20 ),
    inference(avatar_split_clause,[],[f18020,f309,f254,f248,f18025])).

fof(f18020,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f18018,f249])).

fof(f18018,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_12
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f833,f310])).

fof(f833,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_12 ),
    inference(subsumption_resolution,[],[f89,f255])).

fof(f89,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f18009,plain,
    ( ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | spl18_129
    | ~ spl18_1176 ),
    inference(avatar_contradiction_clause,[],[f18008])).

fof(f18008,plain,
    ( $false
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_129
    | ~ spl18_1176 ),
    inference(subsumption_resolution,[],[f18007,f1401])).

fof(f18007,plain,
    ( v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_1176 ),
    inference(subsumption_resolution,[],[f18006,f202])).

fof(f18006,plain,
    ( ~ l1_orders_2(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_1176 ),
    inference(subsumption_resolution,[],[f18005,f274])).

fof(f18005,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_1176 ),
    inference(subsumption_resolution,[],[f18004,f264])).

fof(f18004,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_1176 ),
    inference(subsumption_resolution,[],[f18003,f216])).

fof(f18003,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_1176 ),
    inference(resolution,[],[f18001,f228])).

fof(f228,plain,
    ( ! [X21,X20] :
        ( ~ r1_orders_2(X20,sK9(X21,X20,sK2),sK10(X21,X20,sK2))
        | ~ l1_orders_2(X21)
        | ~ v1_funct_2(sK2,u1_struct_0(X21),u1_struct_0(X20))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | ~ l1_orders_2(X20)
        | v5_orders_3(sK2,X21,X20) )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ r1_orders_2(X1,sK9(X0,X1,X2),sK10(X0,X1,X2))
      | v5_orders_3(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f18001,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK10(sK0,sK1,sK2))
    | ~ spl18_1176 ),
    inference(avatar_component_clause,[],[f18000])).

fof(f18000,plain,
    ( spl18_1176
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK10(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1176])])).

fof(f18002,plain,
    ( spl18_1176
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | spl18_69
    | spl18_129
    | ~ spl18_182
    | ~ spl18_186
    | ~ spl18_218
    | ~ spl18_224 ),
    inference(avatar_split_clause,[],[f17092,f2307,f2255,f1929,f1898,f1400,f800,f273,f263,f245,f215,f201,f187,f18000])).

fof(f245,plain,
    ( spl18_11
  <=> ~ v23_waybel_0(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_11])])).

fof(f1898,plain,
    ( spl18_182
  <=> k1_funct_1(sK2,sK8(sK0,sK1,sK2)) = sK10(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_182])])).

fof(f1929,plain,
    ( spl18_186
  <=> k1_funct_1(sK2,sK7(sK0,sK1,sK2)) = sK9(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_186])])).

fof(f2255,plain,
    ( spl18_218
  <=> m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_218])])).

fof(f2307,plain,
    ( spl18_224
  <=> m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_224])])).

fof(f17092,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK10(sK0,sK1,sK2))
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_129
    | ~ spl18_182
    | ~ spl18_186
    | ~ spl18_218
    | ~ spl18_224 ),
    inference(forward_demodulation,[],[f17091,f1930])).

fof(f1930,plain,
    ( k1_funct_1(sK2,sK7(sK0,sK1,sK2)) = sK9(sK0,sK1,sK2)
    | ~ spl18_186 ),
    inference(avatar_component_clause,[],[f1929])).

fof(f17091,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK7(sK0,sK1,sK2)),sK10(sK0,sK1,sK2))
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_129
    | ~ spl18_182
    | ~ spl18_218
    | ~ spl18_224 ),
    inference(subsumption_resolution,[],[f17090,f1401])).

fof(f17090,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK7(sK0,sK1,sK2)),sK10(sK0,sK1,sK2))
    | v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_182
    | ~ spl18_218
    | ~ spl18_224 ),
    inference(subsumption_resolution,[],[f17089,f202])).

fof(f17089,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK7(sK0,sK1,sK2)),sK10(sK0,sK1,sK2))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_182
    | ~ spl18_218
    | ~ spl18_224 ),
    inference(subsumption_resolution,[],[f17088,f274])).

fof(f17088,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK7(sK0,sK1,sK2)),sK10(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_182
    | ~ spl18_218
    | ~ spl18_224 ),
    inference(subsumption_resolution,[],[f17087,f264])).

fof(f17087,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK7(sK0,sK1,sK2)),sK10(sK0,sK1,sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_182
    | ~ spl18_218
    | ~ spl18_224 ),
    inference(subsumption_resolution,[],[f17086,f216])).

fof(f17086,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK2,sK7(sK0,sK1,sK2)),sK10(sK0,sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_182
    | ~ spl18_218
    | ~ spl18_224 ),
    inference(subsumption_resolution,[],[f17083,f2308])).

fof(f2308,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_224 ),
    inference(avatar_component_clause,[],[f2307])).

fof(f17083,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK1,k1_funct_1(sK2,sK7(sK0,sK1,sK2)),sK10(sK0,sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_182
    | ~ spl18_218 ),
    inference(resolution,[],[f17074,f229])).

fof(f229,plain,
    ( ! [X23,X22] :
        ( r1_orders_2(X23,sK7(X23,X22,sK2),sK8(X23,X22,sK2))
        | ~ l1_orders_2(X23)
        | ~ v1_funct_2(sK2,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | ~ l1_orders_2(X22)
        | v5_orders_3(sK2,X23,X22) )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f125])).

fof(f17074,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,X2,sK8(sK0,sK1,sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK1,k1_funct_1(sK2,X2),sK10(sK0,sK1,sK2)) )
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_182
    | ~ spl18_218 ),
    inference(subsumption_resolution,[],[f1911,f2256])).

fof(f2256,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_218 ),
    inference(avatar_component_clause,[],[f2255])).

fof(f1911,plain,
    ( ! [X2] :
        ( r1_orders_2(sK1,k1_funct_1(sK2,X2),sK10(sK0,sK1,sK2))
        | ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK8(sK0,sK1,sK2)) )
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_182 ),
    inference(superposition,[],[f896,f1899])).

fof(f1899,plain,
    ( k1_funct_1(sK2,sK8(sK0,sK1,sK2)) = sK10(sK0,sK1,sK2)
    | ~ spl18_182 ),
    inference(avatar_component_clause,[],[f1898])).

fof(f896,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,k1_funct_1(sK2,X1),k1_funct_1(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0) )
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69 ),
    inference(subsumption_resolution,[],[f895,f801])).

fof(f895,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,k1_funct_1(sK2,X1),k1_funct_1(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69 ),
    inference(subsumption_resolution,[],[f894,f274])).

fof(f894,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,k1_funct_1(sK2,X1),k1_funct_1(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69 ),
    inference(subsumption_resolution,[],[f893,f264])).

fof(f893,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,k1_funct_1(sK2,X1),k1_funct_1(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69 ),
    inference(duplicate_literal_removal,[],[f892])).

fof(f892,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,k1_funct_1(sK2,X1),k1_funct_1(sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69 ),
    inference(superposition,[],[f885,f234])).

fof(f885,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,k1_funct_1(sK2,X0),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69 ),
    inference(subsumption_resolution,[],[f884,f801])).

fof(f884,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,k1_funct_1(sK2,X0),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f883,f274])).

fof(f883,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,k1_funct_1(sK2,X0),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_14 ),
    inference(subsumption_resolution,[],[f882,f264])).

fof(f882,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,k1_funct_1(sK2,X0),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl18_0
    | ~ spl18_11 ),
    inference(duplicate_literal_removal,[],[f879])).

fof(f879,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,k1_funct_1(sK2,X0),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl18_0
    | ~ spl18_11 ),
    inference(superposition,[],[f870,f234])).

fof(f870,plain,
    ( ! [X4,X3] :
        ( r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X4) )
    | ~ spl18_11 ),
    inference(subsumption_resolution,[],[f86,f246])).

fof(f246,plain,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_11 ),
    inference(avatar_component_clause,[],[f245])).

fof(f86,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
      | ~ r1_orders_2(sK0,X3,X4)
      | v23_waybel_0(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16996,plain,
    ( ~ spl18_198
    | spl18_225 ),
    inference(avatar_contradiction_clause,[],[f16995])).

fof(f16995,plain,
    ( $false
    | ~ spl18_198
    | ~ spl18_225 ),
    inference(subsumption_resolution,[],[f16989,f2311])).

fof(f2311,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_225 ),
    inference(avatar_component_clause,[],[f2310])).

fof(f2310,plain,
    ( spl18_225
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_225])])).

fof(f16989,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_198 ),
    inference(resolution,[],[f2022,f145])).

fof(f2022,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_198 ),
    inference(avatar_component_clause,[],[f2021])).

fof(f2021,plain,
    ( spl18_198
  <=> r2_hidden(sK7(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_198])])).

fof(f16966,plain,
    ( ~ spl18_194
    | spl18_219 ),
    inference(avatar_contradiction_clause,[],[f16965])).

fof(f16965,plain,
    ( $false
    | ~ spl18_194
    | ~ spl18_219 ),
    inference(subsumption_resolution,[],[f16959,f2259])).

fof(f2259,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_219 ),
    inference(avatar_component_clause,[],[f2258])).

fof(f2258,plain,
    ( spl18_219
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_219])])).

fof(f16959,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_194 ),
    inference(resolution,[],[f1993,f145])).

fof(f1993,plain,
    ( r2_hidden(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_194 ),
    inference(avatar_component_clause,[],[f1992])).

fof(f1992,plain,
    ( spl18_194
  <=> r2_hidden(sK8(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_194])])).

fof(f16927,plain,
    ( ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | spl18_69
    | spl18_129
    | spl18_195 ),
    inference(avatar_contradiction_clause,[],[f16926])).

fof(f16926,plain,
    ( $false
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_129
    | ~ spl18_195 ),
    inference(subsumption_resolution,[],[f16925,f1996])).

fof(f1996,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_195 ),
    inference(avatar_component_clause,[],[f1995])).

fof(f1995,plain,
    ( spl18_195
  <=> ~ r2_hidden(sK8(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_195])])).

fof(f16925,plain,
    ( r2_hidden(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f16924,f274])).

fof(f16924,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_hidden(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_69
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f16923,f264])).

fof(f16923,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_hidden(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_69
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f16922,f188])).

fof(f16922,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_hidden(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_69
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f16920,f202])).

fof(f16920,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_hidden(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_8
    | ~ spl18_69
    | ~ spl18_129 ),
    inference(resolution,[],[f1401,f917])).

fof(f917,plain,
    ( ! [X4,X5] :
        ( v5_orders_3(X5,sK0,X4)
        | ~ l1_orders_2(X4)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
        | r2_hidden(sK8(sK0,X4,X5),u1_struct_0(sK0)) )
    | ~ spl18_8
    | ~ spl18_69 ),
    inference(subsumption_resolution,[],[f912,f216])).

fof(f912,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK8(sK0,X4,X5),u1_struct_0(sK0))
        | ~ l1_orders_2(X4)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
        | ~ l1_orders_2(sK0)
        | v5_orders_3(X5,sK0,X4) )
    | ~ spl18_69 ),
    inference(resolution,[],[f863,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X0)
      | v5_orders_3(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14989,plain,(
    ~ spl18_312 ),
    inference(avatar_contradiction_clause,[],[f14988])).

fof(f14988,plain,
    ( $false
    | ~ spl18_312 ),
    inference(subsumption_resolution,[],[f14984,f100])).

fof(f100,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',fc1_xboole_0)).

fof(f14984,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl18_312 ),
    inference(resolution,[],[f3051,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',t7_boole)).

fof(f3051,plain,
    ( r2_hidden(sK15(k1_xboole_0),k1_xboole_0)
    | ~ spl18_312 ),
    inference(avatar_component_clause,[],[f3050])).

fof(f3050,plain,
    ( spl18_312
  <=> r2_hidden(sK15(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_312])])).

fof(f14932,plain,
    ( u1_struct_0(sK0) != k1_xboole_0
    | r2_hidden(sK15(k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK15(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(theory_axiom,[])).

fof(f8153,plain,
    ( ~ spl18_677
    | spl18_437
    | ~ spl18_674 ),
    inference(avatar_split_clause,[],[f8097,f8046,f4666,f8151])).

fof(f4666,plain,
    ( spl18_437
  <=> ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(sK2,sK10(sK1,sK0,k2_funct_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_437])])).

fof(f8046,plain,
    ( spl18_674
  <=> k1_funct_1(sK2,sK10(sK1,sK0,k2_funct_1(sK2))) = sK8(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_674])])).

fof(f8097,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),sK8(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl18_437
    | ~ spl18_674 ),
    inference(superposition,[],[f4667,f8047])).

fof(f8047,plain,
    ( k1_funct_1(sK2,sK10(sK1,sK0,k2_funct_1(sK2))) = sK8(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_674 ),
    inference(avatar_component_clause,[],[f8046])).

fof(f4667,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ spl18_437 ),
    inference(avatar_component_clause,[],[f4666])).

fof(f8073,plain,
    ( spl18_674
    | ~ spl18_662
    | ~ spl18_672 ),
    inference(avatar_split_clause,[],[f8052,f8039,f7717,f8046])).

fof(f7717,plain,
    ( spl18_662
  <=> k1_funct_1(sK2,sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2)))) = sK8(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_662])])).

fof(f8039,plain,
    ( spl18_672
  <=> sK10(sK1,sK0,k2_funct_1(sK2)) = sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_672])])).

fof(f8052,plain,
    ( k1_funct_1(sK2,sK10(sK1,sK0,k2_funct_1(sK2))) = sK8(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_662
    | ~ spl18_672 ),
    inference(superposition,[],[f7718,f8040])).

fof(f8040,plain,
    ( sK10(sK1,sK0,k2_funct_1(sK2)) = sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl18_672 ),
    inference(avatar_component_clause,[],[f8039])).

fof(f7718,plain,
    ( k1_funct_1(sK2,sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2)))) = sK8(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_662 ),
    inference(avatar_component_clause,[],[f7717])).

fof(f8041,plain,
    ( spl18_112
    | spl18_672
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_34
    | ~ spl18_228
    | ~ spl18_652
    | ~ spl18_662 ),
    inference(avatar_split_clause,[],[f8033,f7717,f7574,f2323,f406,f254,f187,f8039,f1225])).

fof(f2323,plain,
    ( spl18_228
  <=> k1_funct_1(k2_funct_1(sK2),sK8(sK1,sK0,k2_funct_1(sK2))) = sK10(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_228])])).

fof(f7574,plain,
    ( spl18_652
  <=> sP13(sK8(sK1,sK0,k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_652])])).

fof(f8033,plain,
    ( ! [X0] :
        ( sK10(sK1,sK0,k2_funct_1(sK2)) = sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_34
    | ~ spl18_228
    | ~ spl18_652
    | ~ spl18_662 ),
    inference(forward_demodulation,[],[f8032,f2324])).

fof(f2324,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK8(sK1,sK0,k2_funct_1(sK2))) = sK10(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_228 ),
    inference(avatar_component_clause,[],[f2323])).

fof(f8032,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK2),sK8(sK1,sK0,k2_funct_1(sK2))) = sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_34
    | ~ spl18_652
    | ~ spl18_662 ),
    inference(forward_demodulation,[],[f7583,f7718])).

fof(f7583,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),X0)
        | k1_xboole_0 = X0
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2))))) = sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2))) )
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_34
    | ~ spl18_652 ),
    inference(forward_demodulation,[],[f7582,f407])).

fof(f7582,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),X0)
        | k1_xboole_0 = X0
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2))))) = sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) )
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_34
    | ~ spl18_652 ),
    inference(forward_demodulation,[],[f7579,f407])).

fof(f7579,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k1_relat_1(sK2),X0)
        | k1_xboole_0 = X0
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2))))) = sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) )
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_652 ),
    inference(resolution,[],[f7575,f598])).

fof(f7575,plain,
    ( sP13(sK8(sK1,sK0,k2_funct_1(sK2)),sK2)
    | ~ spl18_652 ),
    inference(avatar_component_clause,[],[f7574])).

fof(f7719,plain,
    ( spl18_662
    | ~ spl18_652 ),
    inference(avatar_split_clause,[],[f7580,f7574,f7717])).

fof(f7580,plain,
    ( k1_funct_1(sK2,sK14(sK2,sK8(sK1,sK0,k2_funct_1(sK2)))) = sK8(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_652 ),
    inference(resolution,[],[f7575,f138])).

fof(f7576,plain,
    ( spl18_652
    | ~ spl18_0
    | ~ spl18_18
    | ~ spl18_26
    | ~ spl18_236 ),
    inference(avatar_split_clause,[],[f7554,f2376,f360,f283,f187,f7574])).

fof(f2376,plain,
    ( spl18_236
  <=> r2_hidden(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_236])])).

fof(f7554,plain,
    ( sP13(sK8(sK1,sK0,k2_funct_1(sK2)),sK2)
    | ~ spl18_0
    | ~ spl18_18
    | ~ spl18_26
    | ~ spl18_236 ),
    inference(resolution,[],[f2377,f865])).

fof(f865,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK1))
        | sP13(X1,sK2) )
    | ~ spl18_0
    | ~ spl18_18
    | ~ spl18_26 ),
    inference(superposition,[],[f303,f361])).

fof(f2377,plain,
    ( r2_hidden(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl18_236 ),
    inference(avatar_component_clause,[],[f2376])).

fof(f7551,plain,
    ( spl18_89
    | spl18_237
    | ~ spl18_646 ),
    inference(avatar_contradiction_clause,[],[f7550])).

fof(f7550,plain,
    ( $false
    | ~ spl18_89
    | ~ spl18_237
    | ~ spl18_646 ),
    inference(subsumption_resolution,[],[f7548,f2380])).

fof(f2380,plain,
    ( ~ r2_hidden(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl18_237 ),
    inference(avatar_component_clause,[],[f2379])).

fof(f2379,plain,
    ( spl18_237
  <=> ~ r2_hidden(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_237])])).

fof(f7548,plain,
    ( r2_hidden(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl18_89
    | ~ spl18_646 ),
    inference(resolution,[],[f7452,f1028])).

fof(f7452,plain,
    ( m1_subset_1(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl18_646 ),
    inference(avatar_component_clause,[],[f7451])).

fof(f7451,plain,
    ( spl18_646
  <=> m1_subset_1(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_646])])).

fof(f7500,plain,
    ( spl18_66
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_20 ),
    inference(avatar_split_clause,[],[f7494,f309,f273,f263,f254,f187,f795])).

fof(f7494,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f7493,f310])).

fof(f7493,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f577,f264])).

fof(f577,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(resolution,[],[f576,f274])).

fof(f576,plain,
    ( ! [X26,X27] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_2(sK2,X26,X27)
        | k2_relset_1(X26,X27,sK2) != X27
        | v1_funct_2(k2_funct_1(sK2),X27,X26) )
    | ~ spl18_0
    | ~ spl18_12 ),
    inference(subsumption_resolution,[],[f231,f255])).

fof(f231,plain,
    ( ! [X26,X27] :
        ( ~ v1_funct_2(sK2,X26,X27)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v2_funct_1(sK2)
        | k2_relset_1(X26,X27,sK2) != X27
        | v1_funct_2(k2_funct_1(sK2),X27,X26) )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',t31_funct_2)).

fof(f7467,plain,
    ( ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | spl18_59
    | ~ spl18_66
    | ~ spl18_72
    | spl18_647 ),
    inference(avatar_contradiction_clause,[],[f7466])).

fof(f7466,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_647 ),
    inference(subsumption_resolution,[],[f7465,f761])).

fof(f7465,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_647 ),
    inference(subsumption_resolution,[],[f7464,f202])).

fof(f7464,plain,
    ( ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_647 ),
    inference(subsumption_resolution,[],[f7463,f828])).

fof(f7463,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_647 ),
    inference(subsumption_resolution,[],[f7462,f796])).

fof(f7462,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_647 ),
    inference(subsumption_resolution,[],[f7461,f334])).

fof(f7461,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_647 ),
    inference(subsumption_resolution,[],[f7460,f216])).

fof(f7460,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_647 ),
    inference(resolution,[],[f7455,f124])).

fof(f7455,plain,
    ( ~ m1_subset_1(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1))
    | ~ spl18_647 ),
    inference(avatar_component_clause,[],[f7454])).

fof(f7454,plain,
    ( spl18_647
  <=> ~ m1_subset_1(sK8(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_647])])).

fof(f4668,plain,
    ( ~ spl18_437
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | spl18_69
    | ~ spl18_266
    | spl18_325 ),
    inference(avatar_split_clause,[],[f3242,f3227,f2622,f800,f273,f263,f187,f4666])).

fof(f2622,plain,
    ( spl18_266
  <=> m1_subset_1(sK10(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_266])])).

fof(f3227,plain,
    ( spl18_325
  <=> ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK10(sK1,sK0,k2_funct_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_325])])).

fof(f3242,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_266
    | ~ spl18_325 ),
    inference(subsumption_resolution,[],[f3241,f801])).

fof(f3241,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_266
    | ~ spl18_325 ),
    inference(subsumption_resolution,[],[f3240,f2623])).

fof(f2623,plain,
    ( m1_subset_1(sK10(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl18_266 ),
    inference(avatar_component_clause,[],[f2622])).

fof(f3240,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ m1_subset_1(sK10(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_325 ),
    inference(subsumption_resolution,[],[f3239,f274])).

fof(f3239,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK10(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_325 ),
    inference(subsumption_resolution,[],[f3238,f264])).

fof(f3238,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK10(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_325 ),
    inference(superposition,[],[f3228,f234])).

fof(f3228,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ spl18_325 ),
    inference(avatar_component_clause,[],[f3227])).

fof(f3229,plain,
    ( ~ spl18_325
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | spl18_69
    | ~ spl18_246
    | spl18_265 ),
    inference(avatar_split_clause,[],[f2643,f2619,f2487,f800,f273,f263,f187,f3227])).

fof(f2487,plain,
    ( spl18_246
  <=> m1_subset_1(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_246])])).

fof(f2619,plain,
    ( spl18_265
  <=> ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK10(sK1,sK0,k2_funct_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_265])])).

fof(f2643,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_246
    | ~ spl18_265 ),
    inference(subsumption_resolution,[],[f2642,f801])).

fof(f2642,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_246
    | ~ spl18_265 ),
    inference(subsumption_resolution,[],[f2641,f2488])).

fof(f2488,plain,
    ( m1_subset_1(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl18_246 ),
    inference(avatar_component_clause,[],[f2487])).

fof(f2641,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ m1_subset_1(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_265 ),
    inference(subsumption_resolution,[],[f2640,f274])).

fof(f2640,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_265 ),
    inference(subsumption_resolution,[],[f2638,f264])).

fof(f2638,plain,
    ( ~ r1_orders_2(sK1,k1_funct_1(sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_265 ),
    inference(superposition,[],[f2620,f234])).

fof(f2620,plain,
    ( ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ spl18_265 ),
    inference(avatar_component_clause,[],[f2619])).

fof(f2694,plain,
    ( ~ spl18_14
    | ~ spl18_16
    | spl18_33
    | ~ spl18_112 ),
    inference(avatar_contradiction_clause,[],[f2693])).

fof(f2693,plain,
    ( $false
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_33
    | ~ spl18_112 ),
    inference(subsumption_resolution,[],[f2692,f264])).

fof(f2692,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl18_16
    | ~ spl18_33
    | ~ spl18_112 ),
    inference(subsumption_resolution,[],[f2690,f383])).

fof(f383,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | ~ spl18_33 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl18_33
  <=> u1_struct_0(sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_33])])).

fof(f2690,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl18_16
    | ~ spl18_112 ),
    inference(resolution,[],[f1226,f274])).

fof(f1226,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3)))
        | k1_xboole_0 = X3
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),X3) )
    | ~ spl18_112 ),
    inference(avatar_component_clause,[],[f1225])).

fof(f2635,plain,
    ( ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | spl18_59
    | ~ spl18_66
    | ~ spl18_72
    | spl18_267 ),
    inference(avatar_contradiction_clause,[],[f2634])).

fof(f2634,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_267 ),
    inference(subsumption_resolution,[],[f2633,f761])).

fof(f2633,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_267 ),
    inference(subsumption_resolution,[],[f2632,f202])).

fof(f2632,plain,
    ( ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72
    | ~ spl18_267 ),
    inference(subsumption_resolution,[],[f2631,f828])).

fof(f2631,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_267 ),
    inference(subsumption_resolution,[],[f2630,f796])).

fof(f2630,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_267 ),
    inference(subsumption_resolution,[],[f2629,f334])).

fof(f2629,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_8
    | ~ spl18_267 ),
    inference(subsumption_resolution,[],[f2628,f216])).

fof(f2628,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_267 ),
    inference(resolution,[],[f2626,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X0)
      | v5_orders_3(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2626,plain,
    ( ~ m1_subset_1(sK10(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl18_267 ),
    inference(avatar_component_clause,[],[f2625])).

fof(f2625,plain,
    ( spl18_267
  <=> ~ m1_subset_1(sK10(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_267])])).

fof(f2627,plain,
    ( ~ spl18_265
    | ~ spl18_267
    | spl18_11
    | spl18_223
    | ~ spl18_246 ),
    inference(avatar_split_clause,[],[f2614,f2487,f2301,f245,f2625,f2619])).

fof(f2301,plain,
    ( spl18_223
  <=> ~ r1_orders_2(sK0,sK9(sK1,sK0,k2_funct_1(sK2)),sK10(sK1,sK0,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_223])])).

fof(f2614,plain,
    ( ~ m1_subset_1(sK10(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ spl18_11
    | ~ spl18_223
    | ~ spl18_246 ),
    inference(subsumption_resolution,[],[f2305,f2488])).

fof(f2305,plain,
    ( ~ m1_subset_1(sK10(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK9(sK1,sK0,k2_funct_1(sK2))),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK10(sK1,sK0,k2_funct_1(sK2))))
    | ~ m1_subset_1(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl18_11
    | ~ spl18_223 ),
    inference(resolution,[],[f2302,f867])).

fof(f867,plain,
    ( ! [X4,X3] :
        ( r1_orders_2(sK0,X3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl18_11 ),
    inference(subsumption_resolution,[],[f85,f246])).

fof(f85,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r1_orders_2(sK1,k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
      | r1_orders_2(sK0,X3,X4)
      | v23_waybel_0(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2302,plain,
    ( ~ r1_orders_2(sK0,sK9(sK1,sK0,k2_funct_1(sK2)),sK10(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl18_223 ),
    inference(avatar_component_clause,[],[f2301])).

fof(f2489,plain,
    ( spl18_246
    | ~ spl18_244 ),
    inference(avatar_split_clause,[],[f2467,f2454,f2487])).

fof(f2454,plain,
    ( spl18_244
  <=> r2_hidden(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_244])])).

fof(f2467,plain,
    ( m1_subset_1(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl18_244 ),
    inference(resolution,[],[f2455,f145])).

fof(f2455,plain,
    ( r2_hidden(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl18_244 ),
    inference(avatar_component_clause,[],[f2454])).

fof(f2456,plain,
    ( spl18_244
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | spl18_59
    | ~ spl18_66
    | spl18_69
    | ~ spl18_72 ),
    inference(avatar_split_clause,[],[f2408,f827,f800,f795,f760,f333,f215,f201,f2454])).

fof(f2408,plain,
    ( r2_hidden(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_69
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f2407,f202])).

fof(f2407,plain,
    ( ~ l1_orders_2(sK1)
    | r2_hidden(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_69
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f2406,f828])).

fof(f2406,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | r2_hidden(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_69 ),
    inference(subsumption_resolution,[],[f2405,f796])).

fof(f2405,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | r2_hidden(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_69 ),
    inference(subsumption_resolution,[],[f2404,f334])).

fof(f2404,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | r2_hidden(sK9(sK1,sK0,k2_funct_1(sK2)),u1_struct_0(sK0))
    | ~ spl18_8
    | ~ spl18_59
    | ~ spl18_69 ),
    inference(resolution,[],[f918,f761])).

fof(f918,plain,
    ( ! [X6,X7] :
        ( v5_orders_3(X7,X6,sK0)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(sK0))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK0))))
        | ~ l1_orders_2(X6)
        | r2_hidden(sK9(X6,sK0,X7),u1_struct_0(sK0)) )
    | ~ spl18_8
    | ~ spl18_69 ),
    inference(subsumption_resolution,[],[f913,f216])).

fof(f913,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK9(X6,sK0,X7),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(sK0))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK0))))
        | ~ l1_orders_2(X6)
        | v5_orders_3(X7,X6,sK0) )
    | ~ spl18_69 ),
    inference(resolution,[],[f863,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X0)
      | v5_orders_3(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2346,plain,
    ( spl18_230
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | spl18_59
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(avatar_split_clause,[],[f2291,f827,f795,f760,f333,f215,f201,f2344])).

fof(f2291,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2))) = sK9(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f2290,f216])).

fof(f2290,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2))) = sK9(sK1,sK0,k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f2289,f828])).

fof(f2289,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2))) = sK9(sK1,sK0,k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66 ),
    inference(subsumption_resolution,[],[f2288,f796])).

fof(f2288,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2))) = sK9(sK1,sK0,k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_59 ),
    inference(subsumption_resolution,[],[f2281,f202])).

fof(f2281,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_funct_1(k2_funct_1(sK2),sK7(sK1,sK0,k2_funct_1(sK2))) = sK9(sK1,sK0,k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl18_24
    | ~ spl18_59 ),
    inference(resolution,[],[f761,f345])).

fof(f345,plain,
    ( ! [X19,X18] :
        ( v5_orders_3(k2_funct_1(sK2),X19,X18)
        | ~ l1_orders_2(X19)
        | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X19),u1_struct_0(X18))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X18))))
        | k1_funct_1(k2_funct_1(sK2),sK7(X19,X18,k2_funct_1(sK2))) = sK9(X19,X18,k2_funct_1(sK2))
        | ~ l1_orders_2(X18) )
    | ~ spl18_24 ),
    inference(resolution,[],[f334,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_funct_1(X2,sK7(X0,X1,X2)) = sK9(X0,X1,X2)
      | v5_orders_3(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2325,plain,
    ( spl18_228
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | spl18_59
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(avatar_split_clause,[],[f2287,f827,f795,f760,f333,f215,f201,f2323])).

fof(f2287,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK8(sK1,sK0,k2_funct_1(sK2))) = sK10(sK1,sK0,k2_funct_1(sK2))
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f2286,f216])).

fof(f2286,plain,
    ( k1_funct_1(k2_funct_1(sK2),sK8(sK1,sK0,k2_funct_1(sK2))) = sK10(sK1,sK0,k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f2285,f828])).

fof(f2285,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_funct_1(k2_funct_1(sK2),sK8(sK1,sK0,k2_funct_1(sK2))) = sK10(sK1,sK0,k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66 ),
    inference(subsumption_resolution,[],[f2284,f796])).

fof(f2284,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_funct_1(k2_funct_1(sK2),sK8(sK1,sK0,k2_funct_1(sK2))) = sK10(sK1,sK0,k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_59 ),
    inference(subsumption_resolution,[],[f2280,f202])).

fof(f2280,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_funct_1(k2_funct_1(sK2),sK8(sK1,sK0,k2_funct_1(sK2))) = sK10(sK1,sK0,k2_funct_1(sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl18_24
    | ~ spl18_59 ),
    inference(resolution,[],[f761,f346])).

fof(f346,plain,
    ( ! [X21,X20] :
        ( v5_orders_3(k2_funct_1(sK2),X21,X20)
        | ~ l1_orders_2(X21)
        | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X21),u1_struct_0(X20))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | k1_funct_1(k2_funct_1(sK2),sK8(X21,X20,k2_funct_1(sK2))) = sK10(X21,X20,k2_funct_1(sK2))
        | ~ l1_orders_2(X20) )
    | ~ spl18_24 ),
    inference(resolution,[],[f334,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_funct_1(X2,sK8(X0,X1,X2)) = sK10(X0,X1,X2)
      | v5_orders_3(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2303,plain,
    ( ~ spl18_223
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | spl18_59
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(avatar_split_clause,[],[f2295,f827,f795,f760,f333,f215,f201,f2301])).

fof(f2295,plain,
    ( ~ r1_orders_2(sK0,sK9(sK1,sK0,k2_funct_1(sK2)),sK10(sK1,sK0,k2_funct_1(sK2)))
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f2294,f216])).

fof(f2294,plain,
    ( ~ r1_orders_2(sK0,sK9(sK1,sK0,k2_funct_1(sK2)),sK10(sK1,sK0,k2_funct_1(sK2)))
    | ~ l1_orders_2(sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f2293,f828])).

fof(f2293,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ r1_orders_2(sK0,sK9(sK1,sK0,k2_funct_1(sK2)),sK10(sK1,sK0,k2_funct_1(sK2)))
    | ~ l1_orders_2(sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_59
    | ~ spl18_66 ),
    inference(subsumption_resolution,[],[f2292,f796])).

fof(f2292,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ r1_orders_2(sK0,sK9(sK1,sK0,k2_funct_1(sK2)),sK10(sK1,sK0,k2_funct_1(sK2)))
    | ~ l1_orders_2(sK0)
    | ~ spl18_4
    | ~ spl18_24
    | ~ spl18_59 ),
    inference(subsumption_resolution,[],[f2282,f202])).

fof(f2282,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ r1_orders_2(sK0,sK9(sK1,sK0,k2_funct_1(sK2)),sK10(sK1,sK0,k2_funct_1(sK2)))
    | ~ l1_orders_2(sK0)
    | ~ spl18_24
    | ~ spl18_59 ),
    inference(resolution,[],[f761,f347])).

fof(f347,plain,
    ( ! [X23,X22] :
        ( v5_orders_3(k2_funct_1(sK2),X23,X22)
        | ~ l1_orders_2(X23)
        | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | ~ r1_orders_2(X22,sK9(X23,X22,k2_funct_1(sK2)),sK10(X23,X22,k2_funct_1(sK2)))
        | ~ l1_orders_2(X22) )
    | ~ spl18_24 ),
    inference(resolution,[],[f334,f121])).

fof(f2276,plain,
    ( ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | spl18_69
    | spl18_129
    | spl18_199 ),
    inference(avatar_contradiction_clause,[],[f2275])).

fof(f2275,plain,
    ( $false
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_129
    | ~ spl18_199 ),
    inference(subsumption_resolution,[],[f2274,f2025])).

fof(f2025,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_199 ),
    inference(avatar_component_clause,[],[f2024])).

fof(f2024,plain,
    ( spl18_199
  <=> ~ r2_hidden(sK7(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_199])])).

fof(f2274,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_69
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f2273,f274])).

fof(f2273,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_hidden(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_69
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f2272,f264])).

fof(f2272,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_hidden(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_69
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f2271,f188])).

fof(f2271,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_hidden(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_69
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f2270,f202])).

fof(f2270,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_hidden(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_8
    | ~ spl18_69
    | ~ spl18_129 ),
    inference(resolution,[],[f916,f1401])).

fof(f916,plain,
    ( ! [X2,X3] :
        ( v5_orders_3(X3,sK0,X2)
        | ~ l1_orders_2(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | r2_hidden(sK7(sK0,X2,X3),u1_struct_0(sK0)) )
    | ~ spl18_8
    | ~ spl18_69 ),
    inference(subsumption_resolution,[],[f911,f216])).

fof(f911,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK7(sK0,X2,X3),u1_struct_0(sK0))
        | ~ l1_orders_2(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ l1_orders_2(sK0)
        | v5_orders_3(X3,sK0,X2) )
    | ~ spl18_69 ),
    inference(resolution,[],[f863,f126])).

fof(f1931,plain,
    ( spl18_186
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | spl18_129 ),
    inference(avatar_split_clause,[],[f1413,f1400,f273,f263,f215,f201,f187,f1929])).

fof(f1413,plain,
    ( k1_funct_1(sK2,sK7(sK0,sK1,sK2)) = sK9(sK0,sK1,sK2)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f1412,f202])).

fof(f1412,plain,
    ( k1_funct_1(sK2,sK7(sK0,sK1,sK2)) = sK9(sK0,sK1,sK2)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f1411,f274])).

fof(f1411,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_funct_1(sK2,sK7(sK0,sK1,sK2)) = sK9(sK0,sK1,sK2)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f1410,f264])).

fof(f1410,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_funct_1(sK2,sK7(sK0,sK1,sK2)) = sK9(sK0,sK1,sK2)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f1404,f216])).

fof(f1404,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_funct_1(sK2,sK7(sK0,sK1,sK2)) = sK9(sK0,sK1,sK2)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_129 ),
    inference(resolution,[],[f1401,f226])).

fof(f226,plain,
    ( ! [X17,X16] :
        ( v5_orders_3(sK2,X17,X16)
        | ~ l1_orders_2(X17)
        | ~ v1_funct_2(sK2,u1_struct_0(X17),u1_struct_0(X16))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16))))
        | k1_funct_1(sK2,sK7(X17,X16,sK2)) = sK9(X17,X16,sK2)
        | ~ l1_orders_2(X16) )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f119])).

fof(f1900,plain,
    ( spl18_182
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | spl18_129 ),
    inference(avatar_split_clause,[],[f1409,f1400,f273,f263,f215,f201,f187,f1898])).

fof(f1409,plain,
    ( k1_funct_1(sK2,sK8(sK0,sK1,sK2)) = sK10(sK0,sK1,sK2)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f1408,f202])).

fof(f1408,plain,
    ( k1_funct_1(sK2,sK8(sK0,sK1,sK2)) = sK10(sK0,sK1,sK2)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f1407,f274])).

fof(f1407,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_funct_1(sK2,sK8(sK0,sK1,sK2)) = sK10(sK0,sK1,sK2)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f1406,f264])).

fof(f1406,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_funct_1(sK2,sK8(sK0,sK1,sK2)) = sK10(sK0,sK1,sK2)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_129 ),
    inference(subsumption_resolution,[],[f1403,f216])).

fof(f1403,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_funct_1(sK2,sK8(sK0,sK1,sK2)) = sK10(sK0,sK1,sK2)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_129 ),
    inference(resolution,[],[f1401,f227])).

fof(f227,plain,
    ( ! [X19,X18] :
        ( v5_orders_3(sK2,X19,X18)
        | ~ l1_orders_2(X19)
        | ~ v1_funct_2(sK2,u1_struct_0(X19),u1_struct_0(X18))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X18))))
        | k1_funct_1(sK2,sK8(X19,X18,sK2)) = sK10(X19,X18,sK2)
        | ~ l1_orders_2(X18) )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f120])).

fof(f1534,plain,
    ( spl18_142
    | spl18_144
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(avatar_split_clause,[],[f1521,f827,f795,f1532,f1526])).

fof(f1532,plain,
    ( spl18_144
  <=> u1_struct_0(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_144])])).

fof(f1521,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f798,f828])).

fof(f798,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl18_66 ),
    inference(resolution,[],[f796,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',d1_funct_2)).

fof(f1402,plain,
    ( ~ spl18_129
    | ~ spl18_0
    | spl18_3
    | ~ spl18_4
    | spl18_7
    | ~ spl18_8
    | spl18_11
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_24
    | ~ spl18_58
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(avatar_split_clause,[],[f1303,f827,f795,f763,f333,f273,f263,f254,f245,f215,f208,f201,f194,f187,f1400])).

fof(f1303,plain,
    ( ~ v5_orders_3(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_24
    | ~ spl18_58
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f1302,f202])).

fof(f1302,plain,
    ( ~ v5_orders_3(sK2,sK0,sK1)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_24
    | ~ spl18_58
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f1301,f764])).

fof(f1301,plain,
    ( ~ v5_orders_3(sK2,sK0,sK1)
    | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_24
    | ~ spl18_66
    | ~ spl18_72 ),
    inference(subsumption_resolution,[],[f1300,f828])).

fof(f1300,plain,
    ( ~ v5_orders_3(sK2,sK0,sK1)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_24
    | ~ spl18_66 ),
    inference(subsumption_resolution,[],[f1299,f796])).

fof(f1299,plain,
    ( ~ v5_orders_3(sK2,sK0,sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_11
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_24 ),
    inference(subsumption_resolution,[],[f1298,f216])).

fof(f1298,plain,
    ( ~ v5_orders_3(sK2,sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_7
    | ~ spl18_11
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_24 ),
    inference(subsumption_resolution,[],[f1297,f195])).

fof(f1297,plain,
    ( v2_struct_0(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_7
    | ~ spl18_11
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_24 ),
    inference(subsumption_resolution,[],[f1296,f209])).

fof(f1296,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_24 ),
    inference(subsumption_resolution,[],[f1295,f274])).

fof(f1295,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_24 ),
    inference(subsumption_resolution,[],[f1294,f264])).

fof(f1294,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v5_orders_3(sK2,sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_orders_2(sK1)
    | ~ spl18_0
    | ~ spl18_11
    | ~ spl18_12
    | ~ spl18_24 ),
    inference(resolution,[],[f1292,f246])).

fof(f1292,plain,
    ( ! [X0,X1] :
        ( v23_waybel_0(sK2,X1,X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v5_orders_3(sK2,X1,X0)
        | ~ l1_orders_2(X1)
        | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_orders_3(k2_funct_1(sK2),X0,X1)
        | ~ l1_orders_2(X0) )
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_24 ),
    inference(subsumption_resolution,[],[f355,f255])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_funct_1(sK2)
        | ~ v5_orders_3(sK2,X1,X0)
        | ~ l1_orders_2(X1)
        | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_orders_3(k2_funct_1(sK2),X0,X1)
        | v23_waybel_0(sK2,X1,X0) )
    | ~ spl18_0
    | ~ spl18_24 ),
    inference(subsumption_resolution,[],[f336,f188])).

fof(f336,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ v2_funct_1(sK2)
        | ~ v5_orders_3(sK2,X1,X0)
        | ~ l1_orders_2(X1)
        | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_orders_3(k2_funct_1(sK2),X0,X1)
        | v23_waybel_0(sK2,X1,X0) )
    | ~ spl18_24 ),
    inference(resolution,[],[f334,f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(k2_funct_1(X2))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | ~ v5_orders_3(X2,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_orders_3(k2_funct_1(X2),X1,X0)
      | v23_waybel_0(X2,X0,X1) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | ~ v5_orders_3(X2,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | k2_funct_1(X2) != X3
      | ~ v5_orders_3(X3,X1,X0)
      | v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f932,plain,
    ( spl18_80
    | spl18_69 ),
    inference(avatar_split_clause,[],[f915,f800,f930])).

fof(f930,plain,
    ( spl18_80
  <=> r2_hidden(sK15(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_80])])).

fof(f915,plain,
    ( r2_hidden(sK15(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl18_69 ),
    inference(resolution,[],[f863,f143])).

fof(f143,plain,(
    ! [X0] : m1_subset_1(sK15(X0),X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',existence_m1_subset_1)).

fof(f925,plain,
    ( ~ spl18_0
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_20
    | spl18_73 ),
    inference(avatar_contradiction_clause,[],[f924])).

fof(f924,plain,
    ( $false
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_73 ),
    inference(subsumption_resolution,[],[f923,f264])).

fof(f923,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_73 ),
    inference(subsumption_resolution,[],[f922,f310])).

fof(f922,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_73 ),
    inference(subsumption_resolution,[],[f920,f274])).

fof(f920,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_73 ),
    inference(resolution,[],[f825,f579])).

fof(f579,plain,
    ( ! [X28,X29] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X29,X28)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | k2_relset_1(X28,X29,sK2) != X29
        | ~ v1_funct_2(sK2,X28,X29) )
    | ~ spl18_0
    | ~ spl18_12 ),
    inference(subsumption_resolution,[],[f232,f255])).

fof(f232,plain,
    ( ! [X28,X29] :
        ( ~ v1_funct_2(sK2,X28,X29)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | ~ v2_funct_1(sK2)
        | k2_relset_1(X28,X29,sK2) != X29
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X29,X28))) )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f825,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl18_73 ),
    inference(avatar_component_clause,[],[f824])).

fof(f824,plain,
    ( spl18_73
  <=> ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_73])])).

fof(f854,plain,
    ( ~ spl18_16
    | ~ spl18_20
    | spl18_27 ),
    inference(avatar_contradiction_clause,[],[f853])).

fof(f853,plain,
    ( $false
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_27 ),
    inference(subsumption_resolution,[],[f852,f274])).

fof(f852,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl18_20
    | ~ spl18_27 ),
    inference(subsumption_resolution,[],[f847,f364])).

fof(f364,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | ~ spl18_27 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl18_27
  <=> u1_struct_0(sK1) != k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_27])])).

fof(f847,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl18_20 ),
    inference(superposition,[],[f153,f310])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',redefinition_k2_relset_1)).

fof(f844,plain,
    ( ~ spl18_8
    | spl18_75 ),
    inference(avatar_contradiction_clause,[],[f843])).

fof(f843,plain,
    ( $false
    | ~ spl18_8
    | ~ spl18_75 ),
    inference(subsumption_resolution,[],[f842,f216])).

fof(f842,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl18_75 ),
    inference(resolution,[],[f839,f102])).

fof(f102,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',dt_l1_orders_2)).

fof(f839,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl18_75 ),
    inference(avatar_component_clause,[],[f838])).

fof(f838,plain,
    ( spl18_75
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_75])])).

fof(f840,plain,
    ( ~ spl18_75
    | spl18_7
    | ~ spl18_68 ),
    inference(avatar_split_clause,[],[f812,f803,f208,f838])).

fof(f803,plain,
    ( spl18_68
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_68])])).

fof(f812,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl18_7
    | ~ spl18_68 ),
    inference(subsumption_resolution,[],[f809,f209])).

fof(f809,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_68 ),
    inference(resolution,[],[f804,f131])).

fof(f804,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl18_68 ),
    inference(avatar_component_clause,[],[f803])).

fof(f829,plain,
    ( spl18_72
    | ~ spl18_0
    | spl18_3
    | ~ spl18_4
    | spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(avatar_split_clause,[],[f688,f659,f273,f263,f248,f215,f208,f201,f194,f187,f827])).

fof(f659,plain,
    ( spl18_52
  <=> k2_funct_1(sK2) = sK6(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_52])])).

fof(f688,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f687,f249])).

fof(f687,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f686,f216])).

fof(f686,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f685,f195])).

fof(f685,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f684,f209])).

fof(f684,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f683,f274])).

fof(f683,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_14
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f682,f264])).

fof(f682,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f681,f188])).

fof(f681,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_4
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f665,f202])).

fof(f665,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_52 ),
    inference(superposition,[],[f106,f660])).

fof(f660,plain,
    ( k2_funct_1(sK2) = sK6(sK0,sK1,sK2)
    | ~ spl18_52 ),
    inference(avatar_component_clause,[],[f659])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f808,plain,
    ( spl18_68
    | spl18_70
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(avatar_split_clause,[],[f696,f273,f263,f187,f806,f803])).

fof(f696,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl18_0
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f694,f264])).

fof(f694,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl18_0
    | ~ spl18_16 ),
    inference(resolution,[],[f481,f274])).

fof(f481,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | m1_subset_1(k1_funct_1(sK2,X2),X1)
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(X0) )
    | ~ spl18_0 ),
    inference(duplicate_literal_removal,[],[f480])).

fof(f480,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_funct_1(sK2,X2),X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(X0) )
    | ~ spl18_0 ),
    inference(superposition,[],[f233,f234])).

fof(f233,plain,
    ( ! [X30,X31,X32] :
        ( m1_subset_1(k3_funct_2(X30,X31,sK2,X32),X31)
        | ~ v1_funct_2(sK2,X30,X31)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ m1_subset_1(X32,X30)
        | v1_xboole_0(X30) )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f167])).

fof(f797,plain,
    ( spl18_66
    | ~ spl18_0
    | spl18_3
    | ~ spl18_4
    | spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(avatar_split_clause,[],[f680,f659,f273,f263,f248,f215,f208,f201,f194,f187,f795])).

fof(f680,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f679,f249])).

fof(f679,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f678,f216])).

fof(f678,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f677,f195])).

fof(f677,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f676,f209])).

fof(f676,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f675,f274])).

fof(f675,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_14
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f674,f264])).

fof(f674,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f673,f188])).

fof(f673,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_4
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f664,f202])).

fof(f664,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_52 ),
    inference(superposition,[],[f105,f660])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK6(X0,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f765,plain,
    ( spl18_58
    | ~ spl18_0
    | spl18_3
    | ~ spl18_4
    | spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(avatar_split_clause,[],[f672,f659,f273,f263,f248,f215,f208,f201,f194,f187,f763])).

fof(f672,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f671,f249])).

fof(f671,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f670,f202])).

fof(f670,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f669,f195])).

fof(f669,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f668,f209])).

fof(f668,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f667,f274])).

fof(f667,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f666,f264])).

fof(f666,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f663,f216])).

fof(f663,plain,
    ( v5_orders_3(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_52 ),
    inference(superposition,[],[f220,f660])).

fof(f220,plain,
    ( ! [X4,X5] :
        ( v5_orders_3(sK6(X5,X4,sK2),X4,X5)
        | ~ l1_orders_2(X5)
        | ~ v1_funct_2(sK2,u1_struct_0(X5),u1_struct_0(X4))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
        | v2_struct_0(X5)
        | v2_struct_0(X4)
        | ~ l1_orders_2(X4)
        | ~ v23_waybel_0(sK2,X5,X4) )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v5_orders_3(sK6(X0,X1,X2),X1,X0)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f661,plain,
    ( spl18_52
    | ~ spl18_0
    | spl18_3
    | ~ spl18_4
    | spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(avatar_split_clause,[],[f553,f273,f263,f248,f215,f208,f201,f194,f187,f659])).

fof(f553,plain,
    ( k2_funct_1(sK2) = sK6(sK0,sK1,sK2)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f552,f249])).

fof(f552,plain,
    ( k2_funct_1(sK2) = sK6(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f551,f195])).

fof(f551,plain,
    ( v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK6(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f550,f209])).

fof(f550,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK6(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f549,f202])).

fof(f549,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK6(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f548,f264])).

fof(f548,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK6(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_8
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f546,f216])).

fof(f546,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | k2_funct_1(sK2) = sK6(sK0,sK1,sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_16 ),
    inference(resolution,[],[f219,f274])).

fof(f219,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
        | ~ l1_orders_2(X3)
        | ~ v1_funct_2(sK2,u1_struct_0(X3),u1_struct_0(X2))
        | ~ l1_orders_2(X2)
        | v2_struct_0(X3)
        | v2_struct_0(X2)
        | k2_funct_1(sK2) = sK6(X3,X2,sK2)
        | ~ v23_waybel_0(sK2,X3,X2) )
    | ~ spl18_0 ),
    inference(resolution,[],[f188,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | k2_funct_1(X2) = sK6(X0,X1,X2)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f575,plain,
    ( ~ spl18_0
    | spl18_3
    | ~ spl18_4
    | spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | spl18_13
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_13
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f573,f249])).

fof(f573,plain,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_8
    | ~ spl18_13
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f572,f216])).

fof(f572,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_3
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_13
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f571,f195])).

fof(f571,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_7
    | ~ spl18_13
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f570,f209])).

fof(f570,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_4
    | ~ spl18_13
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f569,f202])).

fof(f569,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_13
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f567,f264])).

fof(f567,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl18_0
    | ~ spl18_13
    | ~ spl18_16 ),
    inference(resolution,[],[f563,f274])).

fof(f563,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ l1_orders_2(X1)
        | ~ v23_waybel_0(sK2,X1,X0) )
    | ~ spl18_0
    | ~ spl18_13 ),
    inference(subsumption_resolution,[],[f562,f188])).

fof(f562,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ l1_orders_2(X1)
        | ~ v23_waybel_0(sK2,X1,X0) )
    | ~ spl18_13 ),
    inference(resolution,[],[f252,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f252,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl18_13 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl18_13
  <=> ~ v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_13])])).

fof(f531,plain,
    ( spl18_42
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_18 ),
    inference(avatar_split_clause,[],[f298,f283,f254,f187,f529])).

fof(f529,plain,
    ( spl18_42
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_42])])).

fof(f298,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl18_0
    | ~ spl18_12
    | ~ spl18_18 ),
    inference(subsumption_resolution,[],[f297,f255])).

fof(f297,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl18_0
    | ~ spl18_18 ),
    inference(subsumption_resolution,[],[f289,f188])).

fof(f289,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl18_18 ),
    inference(resolution,[],[f284,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',t55_funct_1)).

fof(f468,plain,
    ( ~ spl18_4
    | spl18_37 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_37 ),
    inference(subsumption_resolution,[],[f466,f202])).

fof(f466,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl18_37 ),
    inference(resolution,[],[f463,f102])).

fof(f463,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl18_37 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl18_37
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_37])])).

fof(f464,plain,
    ( ~ spl18_37
    | spl18_3
    | ~ spl18_32 ),
    inference(avatar_split_clause,[],[f453,f385,f194,f462])).

fof(f385,plain,
    ( spl18_32
  <=> u1_struct_0(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_32])])).

fof(f453,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl18_3
    | ~ spl18_32 ),
    inference(subsumption_resolution,[],[f452,f195])).

fof(f452,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl18_32 ),
    inference(subsumption_resolution,[],[f421,f100])).

fof(f421,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl18_32 ),
    inference(superposition,[],[f131,f386])).

fof(f386,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | ~ spl18_32 ),
    inference(avatar_component_clause,[],[f385])).

fof(f408,plain,
    ( spl18_34
    | ~ spl18_16
    | ~ spl18_30 ),
    inference(avatar_split_clause,[],[f399,f379,f273,f406])).

fof(f379,plain,
    ( spl18_30
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_30])])).

fof(f399,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl18_16
    | ~ spl18_30 ),
    inference(subsumption_resolution,[],[f396,f274])).

fof(f396,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl18_30 ),
    inference(superposition,[],[f380,f152])).

fof(f380,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl18_30 ),
    inference(avatar_component_clause,[],[f379])).

fof(f387,plain,
    ( spl18_30
    | spl18_32
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(avatar_split_clause,[],[f367,f273,f263,f385,f379])).

fof(f367,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f268,f274])).

fof(f268,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl18_14 ),
    inference(resolution,[],[f264,f161])).

fof(f365,plain,
    ( ~ spl18_27
    | ~ spl18_16
    | spl18_21 ),
    inference(avatar_split_clause,[],[f313,f306,f273,f363])).

fof(f306,plain,
    ( spl18_21
  <=> u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_21])])).

fof(f313,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | ~ spl18_16
    | ~ spl18_21 ),
    inference(subsumption_resolution,[],[f312,f274])).

fof(f312,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl18_21 ),
    inference(superposition,[],[f307,f153])).

fof(f307,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl18_21 ),
    inference(avatar_component_clause,[],[f306])).

fof(f335,plain,
    ( spl18_24
    | ~ spl18_0
    | ~ spl18_18 ),
    inference(avatar_split_clause,[],[f296,f283,f187,f333])).

fof(f296,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl18_0
    | ~ spl18_18 ),
    inference(subsumption_resolution,[],[f288,f188])).

fof(f288,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl18_18 ),
    inference(resolution,[],[f284,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',dt_k2_funct_1)).

fof(f311,plain,
    ( spl18_20
    | spl18_11 ),
    inference(avatar_split_clause,[],[f286,f245,f309])).

fof(f286,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl18_11 ),
    inference(subsumption_resolution,[],[f92,f246])).

fof(f92,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f285,plain,
    ( spl18_18
    | ~ spl18_16 ),
    inference(avatar_split_clause,[],[f278,f273,f283])).

fof(f278,plain,
    ( v1_relat_1(sK2)
    | ~ spl18_16 ),
    inference(resolution,[],[f274,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t66_waybel_0.p',cc1_relset_1)).

fof(f275,plain,(
    spl18_16 ),
    inference(avatar_split_clause,[],[f95,f273])).

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f265,plain,(
    spl18_14 ),
    inference(avatar_split_clause,[],[f94,f263])).

fof(f94,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f256,plain,
    ( spl18_10
    | spl18_12 ),
    inference(avatar_split_clause,[],[f91,f254,f248])).

fof(f91,plain,
    ( v2_funct_1(sK2)
    | v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f217,plain,(
    spl18_8 ),
    inference(avatar_split_clause,[],[f99,f215])).

fof(f99,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f210,plain,(
    ~ spl18_7 ),
    inference(avatar_split_clause,[],[f98,f208])).

fof(f98,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f203,plain,(
    spl18_4 ),
    inference(avatar_split_clause,[],[f97,f201])).

fof(f97,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f196,plain,(
    ~ spl18_3 ),
    inference(avatar_split_clause,[],[f96,f194])).

fof(f96,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f189,plain,(
    spl18_0 ),
    inference(avatar_split_clause,[],[f93,f187])).

fof(f93,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
