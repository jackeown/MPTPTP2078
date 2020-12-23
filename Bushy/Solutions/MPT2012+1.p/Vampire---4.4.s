%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_9__t11_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:08 EDT 2019

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 318 expanded)
%              Number of leaves         :   44 ( 141 expanded)
%              Depth                    :    9
%              Number of atoms          :  414 ( 848 expanded)
%              Number of equality atoms :   70 ( 135 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f163,f174,f178,f182,f186,f190,f194,f198,f206,f210,f214,f218,f233,f237,f241,f245,f249,f253,f257,f262,f270,f274,f278,f282,f290,f294,f298,f302])).

fof(f302,plain,
    ( spl6_56
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f283,f176,f172,f161,f300])).

fof(f300,plain,
    ( spl6_56
  <=> u1_struct_0(sK0) = u1_struct_0(k3_waybel_9(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f161,plain,
    ( spl6_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f172,plain,
    ( spl6_4
  <=> l1_waybel_0(k3_waybel_9(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f176,plain,
    ( spl6_6
  <=> v6_waybel_0(k3_waybel_9(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f283,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k3_waybel_9(sK0))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f162,f173,f177,f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | u1_struct_0(X0) = u1_struct_0(k3_waybel_9(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(X1)
      | k3_waybel_9(X0) != X1
      | ~ l1_waybel_0(X1,X0)
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k3_waybel_9(X0) = X1
              | u1_waybel_0(X0,X1) != k3_struct_0(X0)
              | u1_orders_2(X1) != k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
              | u1_struct_0(X0) != u1_struct_0(X1) )
            & ( ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
                & u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
                & u1_struct_0(X0) = u1_struct_0(X1) )
              | k3_waybel_9(X0) != X1 ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k3_waybel_9(X0) = X1
              | u1_waybel_0(X0,X1) != k3_struct_0(X0)
              | u1_orders_2(X1) != k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
              | u1_struct_0(X0) != u1_struct_0(X1) )
            & ( ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
                & u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
                & u1_struct_0(X0) = u1_struct_0(X1) )
              | k3_waybel_9(X0) != X1 ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
              & u1_struct_0(X0) = u1_struct_0(X1) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
              & u1_struct_0(X0) = u1_struct_0(X1) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v6_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v6_waybel_0(X1,X0) )
         => ( k3_waybel_9(X0) = X1
          <=> ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
              & u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',d6_waybel_9)).

fof(f177,plain,
    ( v6_waybel_0(k3_waybel_9(sK0),sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f176])).

fof(f173,plain,
    ( l1_waybel_0(k3_waybel_9(sK0),sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f172])).

fof(f162,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f161])).

fof(f298,plain,
    ( spl6_54
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f284,f176,f172,f161,f296])).

fof(f296,plain,
    ( spl6_54
  <=> u1_orders_2(k3_waybel_9(sK0)) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f284,plain,
    ( u1_orders_2(k3_waybel_9(sK0)) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f162,f173,f177,f152])).

fof(f152,plain,(
    ! [X0] :
      ( ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | u1_orders_2(k3_waybel_9(X0)) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( u1_orders_2(X1) = k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))
      | k3_waybel_9(X0) != X1
      | ~ l1_waybel_0(X1,X0)
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f294,plain,
    ( spl6_52
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f285,f176,f172,f161,f292])).

fof(f292,plain,
    ( spl6_52
  <=> u1_waybel_0(sK0,k3_waybel_9(sK0)) = k3_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f285,plain,
    ( u1_waybel_0(sK0,k3_waybel_9(sK0)) = k3_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f162,f173,f177,f151])).

fof(f151,plain,(
    ! [X0] :
      ( ~ v6_waybel_0(k3_waybel_9(X0),X0)
      | ~ l1_waybel_0(k3_waybel_9(X0),X0)
      | u1_waybel_0(X0,k3_waybel_9(X0)) = k3_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( u1_waybel_0(X0,X1) = k3_struct_0(X0)
      | k3_waybel_9(X0) != X1
      | ~ l1_waybel_0(X1,X0)
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f290,plain,
    ( spl6_50
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f286,f196,f176,f172,f288])).

fof(f288,plain,
    ( spl6_50
  <=> k3_waybel_9(sK0) = g1_waybel_0(sK0,u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0)),u1_waybel_0(sK0,k3_waybel_9(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f196,plain,
    ( spl6_16
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f286,plain,
    ( k3_waybel_9(sK0) = g1_waybel_0(sK0,u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0)),u1_waybel_0(sK0,k3_waybel_9(sK0)))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f197,f173,f177,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ v6_waybel_0(X1,X0)
      | g1_waybel_0(X0,u1_struct_0(X1),u1_orders_2(X1),u1_waybel_0(X0,X1)) = X1
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( g1_waybel_0(X0,u1_struct_0(X1),u1_orders_2(X1),u1_waybel_0(X0,X1)) = X1
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( g1_waybel_0(X0,u1_struct_0(X1),u1_orders_2(X1),u1_waybel_0(X0,X1)) = X1
      | ~ v6_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( v6_waybel_0(X1,X0)
       => g1_waybel_0(X0,u1_struct_0(X1),u1_orders_2(X1),u1_waybel_0(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',abstractness_v6_waybel_0)).

fof(f197,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f196])).

fof(f282,plain,
    ( spl6_48
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f263,f196,f172,f280])).

fof(f280,plain,
    ( spl6_48
  <=> v1_funct_1(u1_waybel_0(sK0,k3_waybel_9(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f263,plain,
    ( v1_funct_1(u1_waybel_0(sK0,k3_waybel_9(sK0)))
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f197,f173,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',dt_u1_waybel_0)).

fof(f278,plain,
    ( spl6_46
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f264,f196,f172,f276])).

fof(f276,plain,
    ( spl6_46
  <=> v1_funct_2(u1_waybel_0(sK0,k3_waybel_9(sK0)),u1_struct_0(k3_waybel_9(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f264,plain,
    ( v1_funct_2(u1_waybel_0(sK0,k3_waybel_9(sK0)),u1_struct_0(k3_waybel_9(sK0)),u1_struct_0(sK0))
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f197,f173,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f274,plain,
    ( spl6_44
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f265,f196,f172,f272])).

fof(f272,plain,
    ( spl6_44
  <=> m1_subset_1(u1_waybel_0(sK0,k3_waybel_9(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k3_waybel_9(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f265,plain,
    ( m1_subset_1(u1_waybel_0(sK0,k3_waybel_9(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k3_waybel_9(sK0)),u1_struct_0(sK0))))
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f197,f173,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f270,plain,
    ( spl6_42
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f266,f196,f172,f268])).

fof(f268,plain,
    ( spl6_42
  <=> l1_orders_2(k3_waybel_9(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f266,plain,
    ( l1_orders_2(k3_waybel_9(sK0))
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f197,f173,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',dt_l1_waybel_0)).

fof(f262,plain,
    ( spl6_40
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f258,f184,f180,f260])).

fof(f260,plain,
    ( spl6_40
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f180,plain,
    ( spl6_8
  <=> l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f184,plain,
    ( spl6_10
  <=> v1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f258,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f181,f185,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',abstractness_v1_orders_2)).

fof(f185,plain,
    ( v1_orders_2(k7_lattice3(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f181,plain,
    ( l1_orders_2(k7_lattice3(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f180])).

fof(f257,plain,
    ( spl6_38
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f223,f180,f255])).

fof(f255,plain,
    ( spl6_38
  <=> l1_struct_0(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f223,plain,
    ( l1_struct_0(k7_lattice3(sK0))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f181,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',dt_l1_orders_2)).

fof(f253,plain,
    ( spl6_36
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f224,f180,f251])).

fof(f251,plain,
    ( spl6_36
  <=> m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f224,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)))))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f181,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',dt_u1_orders_2)).

fof(f249,plain,
    ( spl6_34
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f225,f180,f247])).

fof(f247,plain,
    ( spl6_34
  <=> k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),k3_relset_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f225,plain,
    ( k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),k3_relset_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f181,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',d5_lattice3)).

fof(f245,plain,
    ( spl6_32
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f226,f180,f243])).

fof(f243,plain,
    ( spl6_32
  <=> v1_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f226,plain,
    ( v1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f181,f114])).

fof(f114,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_orders_2(k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',dt_k7_lattice3)).

fof(f241,plain,
    ( spl6_30
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f227,f180,f239])).

fof(f239,plain,
    ( spl6_30
  <=> l1_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f227,plain,
    ( l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f181,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_orders_2(k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f237,plain,
    ( spl6_28
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f228,f180,f235])).

fof(f235,plain,
    ( spl6_28
  <=> v6_waybel_0(k3_waybel_9(k7_lattice3(sK0)),k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f228,plain,
    ( v6_waybel_0(k3_waybel_9(k7_lattice3(sK0)),k7_lattice3(sK0))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f181,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v6_waybel_0(k3_waybel_9(X0),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( l1_waybel_0(k3_waybel_9(X0),X0)
        & v6_waybel_0(k3_waybel_9(X0),X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_waybel_0(k3_waybel_9(X0),X0)
        & v6_waybel_0(k3_waybel_9(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',dt_k3_waybel_9)).

fof(f233,plain,
    ( spl6_26
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f229,f180,f231])).

fof(f231,plain,
    ( spl6_26
  <=> l1_waybel_0(k3_waybel_9(k7_lattice3(sK0)),k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f229,plain,
    ( l1_waybel_0(k3_waybel_9(k7_lattice3(sK0)),k7_lattice3(sK0))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f181,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_waybel_0(k3_waybel_9(X0),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f218,plain,
    ( spl6_24
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f199,f196,f216])).

fof(f216,plain,
    ( spl6_24
  <=> v1_funct_1(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f199,plain,
    ( v1_funct_1(k3_struct_0(sK0))
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f197,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k3_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',dt_k3_struct_0)).

fof(f214,plain,
    ( spl6_22
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f200,f196,f212])).

fof(f212,plain,
    ( spl6_22
  <=> v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f200,plain,
    ( v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f197,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f210,plain,
    ( spl6_20
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f201,f196,f208])).

fof(f208,plain,
    ( spl6_20
  <=> m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f201,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f197,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f206,plain,
    ( spl6_18
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f202,f196,f204])).

fof(f204,plain,
    ( spl6_18
  <=> l1_waybel_0(sK1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f202,plain,
    ( l1_waybel_0(sK1(sK0),sK0)
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f197,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | l1_waybel_0(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( l1_waybel_0(sK1(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
     => l1_waybel_0(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',existence_l1_waybel_0)).

fof(f198,plain,
    ( spl6_16
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f164,f161,f196])).

fof(f164,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f162,f111])).

fof(f194,plain,
    ( spl6_14
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f165,f161,f192])).

fof(f192,plain,
    ( spl6_14
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f165,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f162,f112])).

fof(f190,plain,
    ( spl6_12
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f166,f161,f188])).

fof(f188,plain,
    ( spl6_12
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f166,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f162,f113])).

fof(f186,plain,
    ( spl6_10
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f167,f161,f184])).

fof(f167,plain,
    ( v1_orders_2(k7_lattice3(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f162,f114])).

fof(f182,plain,
    ( spl6_8
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f168,f161,f180])).

fof(f168,plain,
    ( l1_orders_2(k7_lattice3(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f162,f115])).

fof(f178,plain,
    ( spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f169,f161,f176])).

fof(f169,plain,
    ( v6_waybel_0(k3_waybel_9(sK0),sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f162,f116])).

fof(f174,plain,
    ( spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f170,f161,f172])).

fof(f170,plain,
    ( l1_waybel_0(k3_waybel_9(sK0),sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f162,f117])).

fof(f163,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f97,f161])).

fof(f97,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,
    ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f85])).

fof(f85,plain,
    ( ? [X0] :
        ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) != g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0)))
        & l1_orders_2(X0) )
   => ( g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0)))
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) != g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0)))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) = g1_orders_2(u1_struct_0(k3_waybel_9(X0)),u1_orders_2(k3_waybel_9(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t11_waybel_9.p',t11_waybel_9)).

fof(f159,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f98,f157])).

fof(f157,plain,
    ( spl6_1
  <=> g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f98,plain,(
    g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) != g1_orders_2(u1_struct_0(k3_waybel_9(sK0)),u1_orders_2(k3_waybel_9(sK0))) ),
    inference(cnf_transformation,[],[f86])).
%------------------------------------------------------------------------------
