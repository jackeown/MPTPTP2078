%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t22_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:04 EDT 2019

% Result     : Theorem 2.68s
% Output     : Refutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  499 (1114 expanded)
%              Number of leaves         :   86 ( 430 expanded)
%              Depth                    :   20
%              Number of atoms          : 2693 (5042 expanded)
%              Number of equality atoms :   57 ( 169 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25199,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f194,f201,f208,f215,f222,f229,f236,f243,f335,f350,f360,f367,f389,f407,f419,f427,f452,f484,f715,f778,f785,f808,f823,f889,f912,f945,f1135,f1179,f1190,f1213,f1607,f1608,f1701,f1828,f2090,f2110,f2182,f3015,f3451,f3604,f3656,f3683,f4892,f6100,f6151,f6193,f6415,f6430,f6505,f23827,f23851,f23973,f24013,f24241,f24253,f24624,f25195])).

fof(f25195,plain,
    ( ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_24
    | ~ spl19_66
    | ~ spl19_70
    | ~ spl19_180
    | ~ spl19_200
    | spl19_501 ),
    inference(avatar_contradiction_clause,[],[f25194])).

fof(f25194,plain,
    ( $false
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_24
    | ~ spl19_66
    | ~ spl19_70
    | ~ spl19_180
    | ~ spl19_200
    | ~ spl19_501 ),
    inference(subsumption_resolution,[],[f25190,f1966])).

fof(f1966,plain,
    ( r2_hidden(sK10(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_180 ),
    inference(avatar_component_clause,[],[f1965])).

fof(f1965,plain,
    ( spl19_180
  <=> r2_hidden(sK10(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_180])])).

fof(f25190,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_24
    | ~ spl19_66
    | ~ spl19_70
    | ~ spl19_200
    | ~ spl19_501 ),
    inference(resolution,[],[f6150,f24678])).

fof(f24678,plain,
    ( ! [X2] :
        ( r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),X2),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_24
    | ~ spl19_66
    | ~ spl19_70
    | ~ spl19_200 ),
    inference(resolution,[],[f2109,f24219])).

fof(f24219,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(k12_lattice3(sK0,X2,X3),k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_24
    | ~ spl19_66
    | ~ spl19_70 ),
    inference(subsumption_resolution,[],[f24025,f366])).

fof(f366,plain,
    ( v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_24 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl19_24
  <=> v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_24])])).

fof(f24025,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(k12_lattice3(sK0,X2,X3),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_66
    | ~ spl19_70 ),
    inference(subsumption_resolution,[],[f23898,f768])).

fof(f768,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_66 ),
    inference(avatar_component_clause,[],[f767])).

fof(f767,plain,
    ( spl19_66
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_66])])).

fof(f23898,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X3,k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(k12_lattice3(sK0,X2,X3),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_70 ),
    inference(resolution,[],[f798,f319])).

fof(f319,plain,
    ( ! [X45,X43,X44] :
        ( ~ v13_waybel_0(X43,sK0)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X44,X43)
        | ~ r2_hidden(X45,X43)
        | r2_hidden(k12_lattice3(sK0,X44,X45),X43)
        | ~ v2_waybel_0(X43,sK0) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f318,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t4_subset)).

fof(f318,plain,
    ( ! [X45,X43,X44] :
        ( ~ v13_waybel_0(X43,sK0)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X45,u1_struct_0(sK0))
        | ~ r2_hidden(X44,X43)
        | ~ r2_hidden(X45,X43)
        | r2_hidden(k12_lattice3(sK0,X44,X45),X43)
        | ~ v2_waybel_0(X43,sK0) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f317,f171])).

fof(f317,plain,
    ( ! [X45,X43,X44] :
        ( ~ v13_waybel_0(X43,sK0)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X44,u1_struct_0(sK0))
        | ~ m1_subset_1(X45,u1_struct_0(sK0))
        | ~ r2_hidden(X44,X43)
        | ~ r2_hidden(X45,X43)
        | r2_hidden(k12_lattice3(sK0,X44,X45),X43)
        | ~ v2_waybel_0(X43,sK0) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f316,f214])).

fof(f214,plain,
    ( v5_orders_2(sK0)
    | ~ spl19_6 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl19_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_6])])).

fof(f316,plain,
    ( ! [X45,X43,X44] :
        ( ~ v5_orders_2(sK0)
        | ~ v13_waybel_0(X43,sK0)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X44,u1_struct_0(sK0))
        | ~ m1_subset_1(X45,u1_struct_0(sK0))
        | ~ r2_hidden(X44,X43)
        | ~ r2_hidden(X45,X43)
        | r2_hidden(k12_lattice3(sK0,X44,X45),X43)
        | ~ v2_waybel_0(X43,sK0) )
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f269,f221])).

fof(f221,plain,
    ( v2_lattice3(sK0)
    | ~ spl19_8 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl19_8
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_8])])).

fof(f269,plain,
    ( ! [X45,X43,X44] :
        ( ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v13_waybel_0(X43,sK0)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X44,u1_struct_0(sK0))
        | ~ m1_subset_1(X45,u1_struct_0(sK0))
        | ~ r2_hidden(X44,X43)
        | ~ r2_hidden(X45,X43)
        | r2_hidden(k12_lattice3(sK0,X44,X45),X43)
        | ~ v2_waybel_0(X43,sK0) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f151])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k12_lattice3(X0,X2,X3),X1)
      | ~ v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t41_waybel_0)).

fof(f228,plain,
    ( l1_orders_2(sK0)
    | ~ spl19_10 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl19_10
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_10])])).

fof(f798,plain,
    ( v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_70 ),
    inference(avatar_component_clause,[],[f797])).

fof(f797,plain,
    ( spl19_70
  <=> v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_70])])).

fof(f2109,plain,
    ( r2_hidden(sK9(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_200 ),
    inference(avatar_component_clause,[],[f2108])).

fof(f2108,plain,
    ( spl19_200
  <=> r2_hidden(sK9(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_200])])).

fof(f6150,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_501 ),
    inference(avatar_component_clause,[],[f6149])).

fof(f6149,plain,
    ( spl19_501
  <=> ~ r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_501])])).

fof(f24624,plain,
    ( spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | spl19_19
    | spl19_199 ),
    inference(avatar_contradiction_clause,[],[f24623])).

fof(f24623,plain,
    ( $false
    | ~ spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_19
    | ~ spl19_199 ),
    inference(subsumption_resolution,[],[f24024,f343])).

fof(f343,plain,
    ( ~ v1_waybel_7(sK1,sK0)
    | ~ spl19_19 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl19_19
  <=> ~ v1_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_19])])).

fof(f24024,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_199 ),
    inference(subsumption_resolution,[],[f24023,f200])).

fof(f200,plain,
    ( v3_orders_2(sK0)
    | ~ spl19_2 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl19_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).

fof(f24023,plain,
    ( ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_199 ),
    inference(subsumption_resolution,[],[f24022,f334])).

fof(f334,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_16 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl19_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_16])])).

fof(f24022,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_199 ),
    inference(subsumption_resolution,[],[f24021,f242])).

fof(f242,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ spl19_14 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl19_14
  <=> v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_14])])).

fof(f24021,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_199 ),
    inference(subsumption_resolution,[],[f24020,f235])).

fof(f235,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl19_12 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl19_12
  <=> v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_12])])).

fof(f24020,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_199 ),
    inference(subsumption_resolution,[],[f24019,f193])).

fof(f193,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl19_1
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f24019,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_199 ),
    inference(subsumption_resolution,[],[f24018,f228])).

fof(f24018,plain,
    ( ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_199 ),
    inference(subsumption_resolution,[],[f24017,f221])).

fof(f24017,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_199 ),
    inference(subsumption_resolution,[],[f24016,f214])).

fof(f24016,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_4
    | ~ spl19_199 ),
    inference(subsumption_resolution,[],[f2111,f207])).

fof(f207,plain,
    ( v4_orders_2(sK0)
    | ~ spl19_4 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl19_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f2111,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_199 ),
    inference(resolution,[],[f2103,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',d1_waybel_7)).

fof(f2103,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl19_199 ),
    inference(avatar_component_clause,[],[f2102])).

fof(f2102,plain,
    ( spl19_199
  <=> ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_199])])).

fof(f24253,plain,
    ( spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | spl19_19
    | spl19_179 ),
    inference(avatar_contradiction_clause,[],[f24252])).

fof(f24252,plain,
    ( $false
    | ~ spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_19
    | ~ spl19_179 ),
    inference(subsumption_resolution,[],[f24251,f343])).

fof(f24251,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_179 ),
    inference(subsumption_resolution,[],[f24250,f200])).

fof(f24250,plain,
    ( ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_179 ),
    inference(subsumption_resolution,[],[f24249,f334])).

fof(f24249,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_179 ),
    inference(subsumption_resolution,[],[f24248,f242])).

fof(f24248,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_179 ),
    inference(subsumption_resolution,[],[f24247,f235])).

fof(f24247,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_1
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_179 ),
    inference(subsumption_resolution,[],[f24246,f193])).

fof(f24246,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_179 ),
    inference(subsumption_resolution,[],[f24245,f228])).

fof(f24245,plain,
    ( ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_179 ),
    inference(subsumption_resolution,[],[f24244,f221])).

fof(f24244,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_179 ),
    inference(subsumption_resolution,[],[f24243,f214])).

fof(f24243,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_4
    | ~ spl19_179 ),
    inference(subsumption_resolution,[],[f24242,f207])).

fof(f24242,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_179 ),
    inference(resolution,[],[f1928,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1928,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl19_179 ),
    inference(avatar_component_clause,[],[f1927])).

fof(f1927,plain,
    ( spl19_179
  <=> ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_179])])).

fof(f24241,plain,
    ( ~ spl19_179
    | ~ spl19_40
    | spl19_113
    | spl19_181 ),
    inference(avatar_split_clause,[],[f24135,f1968,f1177,f444,f1927])).

fof(f444,plain,
    ( spl19_40
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_40])])).

fof(f1177,plain,
    ( spl19_113
  <=> ~ r2_hidden(sK10(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_113])])).

fof(f1968,plain,
    ( spl19_181
  <=> ~ r2_hidden(sK10(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_181])])).

fof(f24135,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl19_40
    | ~ spl19_113
    | ~ spl19_181 ),
    inference(subsumption_resolution,[],[f24134,f1969])).

fof(f1969,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_181 ),
    inference(avatar_component_clause,[],[f1968])).

fof(f24134,plain,
    ( r2_hidden(sK10(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl19_40
    | ~ spl19_113 ),
    inference(resolution,[],[f1178,f445])).

fof(f445,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl19_40 ),
    inference(avatar_component_clause,[],[f444])).

fof(f1178,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),sK1)
    | ~ spl19_113 ),
    inference(avatar_component_clause,[],[f1177])).

fof(f24013,plain,
    ( ~ spl19_16
    | spl19_291
    | spl19_519
    | ~ spl19_1052 ),
    inference(avatar_contradiction_clause,[],[f24012])).

fof(f24012,plain,
    ( $false
    | ~ spl19_16
    | ~ spl19_291
    | ~ spl19_519
    | ~ spl19_1052 ),
    inference(subsumption_resolution,[],[f24011,f6504])).

fof(f6504,plain,
    ( ~ r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl19_519 ),
    inference(avatar_component_clause,[],[f6503])).

fof(f6503,plain,
    ( spl19_519
  <=> ~ r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_519])])).

fof(f24011,plain,
    ( r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl19_16
    | ~ spl19_291
    | ~ spl19_1052 ),
    inference(resolution,[],[f23972,f7558])).

fof(f7558,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) )
    | ~ spl19_16
    | ~ spl19_291 ),
    inference(subsumption_resolution,[],[f7557,f334])).

fof(f7557,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl19_291 ),
    inference(superposition,[],[f3016,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',involutiveness_k3_subset_1)).

fof(f3016,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) )
    | ~ spl19_291 ),
    inference(resolution,[],[f3011,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t2_subset)).

fof(f3011,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl19_291 ),
    inference(avatar_component_clause,[],[f3010])).

fof(f3010,plain,
    ( spl19_291
  <=> ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_291])])).

fof(f23972,plain,
    ( m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl19_1052 ),
    inference(avatar_component_clause,[],[f23971])).

fof(f23971,plain,
    ( spl19_1052
  <=> m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1052])])).

fof(f23973,plain,
    ( spl19_1052
    | ~ spl19_424 ),
    inference(avatar_split_clause,[],[f23939,f4887,f23971])).

fof(f4887,plain,
    ( spl19_424
  <=> r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_424])])).

fof(f23939,plain,
    ( m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl19_424 ),
    inference(resolution,[],[f4888,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t1_subset)).

fof(f4888,plain,
    ( r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl19_424 ),
    inference(avatar_component_clause,[],[f4887])).

fof(f23851,plain,
    ( ~ spl19_10
    | ~ spl19_66
    | spl19_71
    | ~ spl19_774 ),
    inference(avatar_contradiction_clause,[],[f23850])).

fof(f23850,plain,
    ( $false
    | ~ spl19_10
    | ~ spl19_66
    | ~ spl19_71
    | ~ spl19_774 ),
    inference(subsumption_resolution,[],[f23849,f801])).

fof(f801,plain,
    ( ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_71 ),
    inference(avatar_component_clause,[],[f800])).

fof(f800,plain,
    ( spl19_71
  <=> ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_71])])).

fof(f23849,plain,
    ( v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_10
    | ~ spl19_66
    | ~ spl19_774 ),
    inference(subsumption_resolution,[],[f23828,f768])).

fof(f23828,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_10
    | ~ spl19_774 ),
    inference(resolution,[],[f12086,f253])).

fof(f253,plain,
    ( ! [X15] :
        ( ~ r2_hidden(sK6(sK0,X15),X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | v13_waybel_0(X15,sK0) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK6(X0,X1),X1)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',d20_waybel_0)).

fof(f12086,plain,
    ( r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_774 ),
    inference(avatar_component_clause,[],[f12085])).

fof(f12085,plain,
    ( spl19_774
  <=> r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_774])])).

fof(f23827,plain,
    ( ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_40
    | ~ spl19_66
    | spl19_71
    | ~ spl19_204
    | spl19_517
    | spl19_775 ),
    inference(avatar_contradiction_clause,[],[f23826])).

fof(f23826,plain,
    ( $false
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_40
    | ~ spl19_66
    | ~ spl19_71
    | ~ spl19_204
    | ~ spl19_517
    | ~ spl19_775 ),
    inference(subsumption_resolution,[],[f11550,f12083])).

fof(f12083,plain,
    ( ~ r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_775 ),
    inference(avatar_component_clause,[],[f12082])).

fof(f12082,plain,
    ( spl19_775
  <=> ~ r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_775])])).

fof(f11550,plain,
    ( r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_40
    | ~ spl19_66
    | ~ spl19_71
    | ~ spl19_204
    | ~ spl19_517 ),
    inference(subsumption_resolution,[],[f11549,f801])).

fof(f11549,plain,
    ( r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_40
    | ~ spl19_66
    | ~ spl19_204
    | ~ spl19_517 ),
    inference(subsumption_resolution,[],[f11548,f768])).

fof(f11548,plain,
    ( r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_40
    | ~ spl19_204
    | ~ spl19_517 ),
    inference(subsumption_resolution,[],[f11542,f6429])).

fof(f6429,plain,
    ( ~ r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl19_517 ),
    inference(avatar_component_clause,[],[f6428])).

fof(f6428,plain,
    ( spl19_517
  <=> ~ r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_517])])).

fof(f11542,plain,
    ( r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_40
    | ~ spl19_204 ),
    inference(resolution,[],[f4533,f2181])).

fof(f2181,plain,
    ( m1_subset_1(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl19_204 ),
    inference(avatar_component_clause,[],[f2180])).

fof(f2180,plain,
    ( spl19_204
  <=> m1_subset_1(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_204])])).

fof(f4533,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,X0),k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v13_waybel_0(X0,sK0) )
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_40 ),
    inference(subsumption_resolution,[],[f4532,f228])).

fof(f4532,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),sK1)
        | r2_hidden(sK6(sK0,X0),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v13_waybel_0(X0,sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_40 ),
    inference(duplicate_literal_removal,[],[f4531])).

fof(f4531,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),sK1)
        | r2_hidden(sK6(sK0,X0),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v13_waybel_0(X0,sK0) )
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_40 ),
    inference(resolution,[],[f2429,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f2429,plain,
    ( ! [X15] :
        ( ~ m1_subset_1(sK6(sK0,X15),u1_struct_0(sK0))
        | r2_hidden(sK5(sK0,X15),sK1)
        | r2_hidden(sK6(sK0,X15),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(sK5(sK0,X15),u1_struct_0(sK0))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | v13_waybel_0(X15,sK0) )
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_40 ),
    inference(resolution,[],[f620,f252])).

fof(f252,plain,
    ( ! [X14] :
        ( r1_orders_2(sK0,sK5(sK0,X14),sK6(sK0,X14))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | v13_waybel_0(X14,sK0) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_orders_2(X0,sK5(X0,X1),sK6(X0,X1))
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f620,plain,
    ( ! [X2,X1] :
        ( ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_40 ),
    inference(resolution,[],[f566,f445])).

fof(f566,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X0,sK1) )
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16 ),
    inference(subsumption_resolution,[],[f563,f334])).

fof(f563,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl19_10
    | ~ spl19_14 ),
    inference(resolution,[],[f284,f242])).

fof(f284,plain,
    ( ! [X24,X23,X22] :
        ( ~ v12_waybel_0(X22,sK0)
        | ~ m1_subset_1(X24,u1_struct_0(sK0))
        | ~ r2_hidden(X23,X22)
        | ~ r1_orders_2(sK0,X24,X23)
        | r2_hidden(X24,X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f258,f171])).

fof(f258,plain,
    ( ! [X24,X23,X22] :
        ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | ~ m1_subset_1(X24,u1_struct_0(sK0))
        | ~ r2_hidden(X23,X22)
        | ~ r1_orders_2(sK0,X24,X23)
        | r2_hidden(X24,X22)
        | ~ v12_waybel_0(X22,sK0) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r2_hidden(X3,X1)
      | ~ v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',d19_waybel_0)).

fof(f6505,plain,
    ( ~ spl19_519
    | ~ spl19_194
    | ~ spl19_320 ),
    inference(avatar_split_clause,[],[f3780,f3602,f2088,f6503])).

fof(f2088,plain,
    ( spl19_194
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_194])])).

fof(f3602,plain,
    ( spl19_320
  <=> r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_320])])).

fof(f3780,plain,
    ( ~ r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl19_194
    | ~ spl19_320 ),
    inference(superposition,[],[f3641,f2089])).

fof(f2089,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_194 ),
    inference(avatar_component_clause,[],[f2088])).

fof(f3641,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k4_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl19_320 ),
    inference(resolution,[],[f3610,f185])).

fof(f185,plain,(
    ! [X0,X3,X1] :
      ( sP16(X3,X1,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f176])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( sP16(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',d5_xboole_0)).

fof(f3610,plain,
    ( ! [X2] : ~ sP16(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1),X2)
    | ~ spl19_320 ),
    inference(resolution,[],[f3603,f174])).

fof(f174,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ sP16(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3603,plain,
    ( r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_320 ),
    inference(avatar_component_clause,[],[f3602])).

fof(f6430,plain,
    ( ~ spl19_517
    | ~ spl19_16
    | spl19_515 ),
    inference(avatar_split_clause,[],[f6421,f6413,f333,f6428])).

fof(f6413,plain,
    ( spl19_515
  <=> ~ r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_515])])).

fof(f6421,plain,
    ( ~ r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl19_16
    | ~ spl19_515 ),
    inference(subsumption_resolution,[],[f6420,f334])).

fof(f6420,plain,
    ( ~ r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_515 ),
    inference(superposition,[],[f6414,f158])).

fof(f6414,plain,
    ( ~ r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl19_515 ),
    inference(avatar_component_clause,[],[f6413])).

fof(f6415,plain,
    ( ~ spl19_515
    | ~ spl19_164
    | ~ spl19_194 ),
    inference(avatar_split_clause,[],[f2836,f2088,f1826,f6413])).

fof(f1826,plain,
    ( spl19_164
  <=> r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_164])])).

fof(f2836,plain,
    ( ~ r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl19_164
    | ~ spl19_194 ),
    inference(superposition,[],[f2042,f2089])).

fof(f2042,plain,
    ( ! [X0] : ~ r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k4_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl19_164 ),
    inference(resolution,[],[f1841,f185])).

fof(f1841,plain,
    ( ! [X2] : ~ sP16(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1),X2)
    | ~ spl19_164 ),
    inference(resolution,[],[f1827,f174])).

fof(f1827,plain,
    ( r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_164 ),
    inference(avatar_component_clause,[],[f1826])).

fof(f6193,plain,
    ( ~ spl19_28
    | ~ spl19_68
    | ~ spl19_492 ),
    inference(avatar_contradiction_clause,[],[f6192])).

fof(f6192,plain,
    ( $false
    | ~ spl19_28
    | ~ spl19_68
    | ~ spl19_492 ),
    inference(subsumption_resolution,[],[f6190,f777])).

fof(f777,plain,
    ( r2_hidden(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_68 ),
    inference(avatar_component_clause,[],[f776])).

fof(f776,plain,
    ( spl19_68
  <=> r2_hidden(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_68])])).

fof(f6190,plain,
    ( ~ r2_hidden(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_28
    | ~ spl19_492 ),
    inference(superposition,[],[f6177,f388])).

fof(f388,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl19_28 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl19_28
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_28])])).

fof(f6177,plain,
    ( ! [X0] : ~ r2_hidden(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k4_xboole_0(X0,sK1))
    | ~ spl19_492 ),
    inference(resolution,[],[f6115,f185])).

fof(f6115,plain,
    ( ! [X7] : ~ sP16(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1,X7)
    | ~ spl19_492 ),
    inference(resolution,[],[f6099,f174])).

fof(f6099,plain,
    ( r2_hidden(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl19_492 ),
    inference(avatar_component_clause,[],[f6098])).

fof(f6098,plain,
    ( spl19_492
  <=> r2_hidden(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_492])])).

fof(f6151,plain,
    ( ~ spl19_501
    | ~ spl19_28
    | ~ spl19_118 ),
    inference(avatar_split_clause,[],[f1431,f1211,f387,f6149])).

fof(f1211,plain,
    ( spl19_118
  <=> r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_118])])).

fof(f1431,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_28
    | ~ spl19_118 ),
    inference(superposition,[],[f1373,f388])).

fof(f1373,plain,
    ( ! [X0] : ~ r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),k4_xboole_0(X0,sK1))
    | ~ spl19_118 ),
    inference(resolution,[],[f1220,f185])).

fof(f1220,plain,
    ( ! [X3] : ~ sP16(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1,X3)
    | ~ spl19_118 ),
    inference(resolution,[],[f1212,f174])).

fof(f1212,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | ~ spl19_118 ),
    inference(avatar_component_clause,[],[f1211])).

fof(f6100,plain,
    ( spl19_492
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_326
    | ~ spl19_328
    | ~ spl19_426 ),
    inference(avatar_split_clause,[],[f4910,f4890,f3681,f3654,f227,f220,f213,f6098])).

fof(f3654,plain,
    ( spl19_326
  <=> m1_subset_1(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_326])])).

fof(f3681,plain,
    ( spl19_328
  <=> m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_328])])).

fof(f4890,plain,
    ( spl19_426
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0),sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_426])])).

fof(f4910,plain,
    ( r2_hidden(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_326
    | ~ spl19_328
    | ~ spl19_426 ),
    inference(subsumption_resolution,[],[f4909,f3682])).

fof(f3682,plain,
    ( m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl19_328 ),
    inference(avatar_component_clause,[],[f3681])).

fof(f4909,plain,
    ( r2_hidden(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_326
    | ~ spl19_426 ),
    inference(subsumption_resolution,[],[f4908,f3655])).

fof(f3655,plain,
    ( m1_subset_1(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl19_326 ),
    inference(avatar_component_clause,[],[f3654])).

fof(f4908,plain,
    ( r2_hidden(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_426 ),
    inference(duplicate_literal_removal,[],[f4901])).

fof(f4901,plain,
    ( r2_hidden(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_426 ),
    inference(resolution,[],[f4891,f442])).

fof(f442,plain,
    ( ! [X6,X5] :
        ( r1_orders_2(sK0,k12_lattice3(sK0,X6,X5),X5)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f441,f214])).

fof(f441,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X6,X5),X5) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f440,f228])).

fof(f440,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X6,X5),X5) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f431,f221])).

fof(f431,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X6,X5),X5) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(duplicate_literal_removal,[],[f430])).

fof(f430,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X6,X5),X5) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(resolution,[],[f323,f182])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) ) ),
    inference(equality_resolution,[],[f146])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t23_yellow_0)).

fof(f323,plain,
    ( ! [X50,X51] :
        ( m1_subset_1(k12_lattice3(sK0,X50,X51),u1_struct_0(sK0))
        | ~ m1_subset_1(X51,u1_struct_0(sK0))
        | ~ m1_subset_1(X50,u1_struct_0(sK0)) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f322,f214])).

fof(f322,plain,
    ( ! [X50,X51] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X50,u1_struct_0(sK0))
        | ~ m1_subset_1(X51,u1_struct_0(sK0))
        | m1_subset_1(k12_lattice3(sK0,X50,X51),u1_struct_0(sK0)) )
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f272,f221])).

fof(f272,plain,
    ( ! [X50,X51] :
        ( ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X50,u1_struct_0(sK0))
        | ~ m1_subset_1(X51,u1_struct_0(sK0))
        | m1_subset_1(k12_lattice3(sK0,X50,X51),u1_struct_0(sK0)) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',dt_k12_lattice3)).

fof(f4891,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0),sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl19_426 ),
    inference(avatar_component_clause,[],[f4890])).

fof(f4892,plain,
    ( spl19_424
    | spl19_426
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_18
    | spl19_25
    | ~ spl19_40
    | ~ spl19_66
    | ~ spl19_328 ),
    inference(avatar_split_clause,[],[f3712,f3681,f767,f444,f362,f339,f333,f241,f234,f227,f220,f213,f206,f199,f4890,f4887])).

fof(f339,plain,
    ( spl19_18
  <=> v1_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_18])])).

fof(f362,plain,
    ( spl19_25
  <=> ~ v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_25])])).

fof(f3712,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0),sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_18
    | ~ spl19_25
    | ~ spl19_40
    | ~ spl19_66
    | ~ spl19_328 ),
    inference(subsumption_resolution,[],[f3711,f3682])).

fof(f3711,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0),sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_18
    | ~ spl19_25
    | ~ spl19_40
    | ~ spl19_66
    | ~ spl19_328 ),
    inference(duplicate_literal_removal,[],[f3705])).

fof(f3705,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0),sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_18
    | ~ spl19_25
    | ~ spl19_40
    | ~ spl19_66
    | ~ spl19_328 ),
    inference(resolution,[],[f3697,f1942])).

fof(f1942,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k12_lattice3(sK0,X1,X0),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_18
    | ~ spl19_40 ),
    inference(subsumption_resolution,[],[f1937,f323])).

fof(f1937,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | r2_hidden(X0,sK1)
        | r2_hidden(k12_lattice3(sK0,X1,X0),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(k12_lattice3(sK0,X1,X0),u1_struct_0(sK0)) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_18
    | ~ spl19_40 ),
    inference(resolution,[],[f1741,f445])).

fof(f1741,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_18 ),
    inference(subsumption_resolution,[],[f597,f340])).

fof(f340,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ spl19_18 ),
    inference(avatar_component_clause,[],[f339])).

fof(f597,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK1)
        | r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ v1_waybel_7(sK1,sK0) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16 ),
    inference(subsumption_resolution,[],[f596,f334])).

fof(f596,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK1)
        | r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ v1_waybel_7(sK1,sK0) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14 ),
    inference(subsumption_resolution,[],[f595,f242])).

fof(f595,plain,
    ( ! [X0,X1] :
        ( ~ v12_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK1)
        | r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ v1_waybel_7(sK1,sK0) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12 ),
    inference(resolution,[],[f303,f235])).

fof(f303,plain,
    ( ! [X30,X28,X29] :
        ( ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X29,u1_struct_0(sK0))
        | ~ m1_subset_1(X30,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X29,X30),X28)
        | r2_hidden(X29,X28)
        | r2_hidden(X30,X28)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f302,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t7_boole)).

fof(f302,plain,
    ( ! [X30,X28,X29] :
        ( v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X29,u1_struct_0(sK0))
        | ~ m1_subset_1(X30,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X29,X30),X28)
        | r2_hidden(X29,X28)
        | r2_hidden(X30,X28)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f301,f200])).

fof(f301,plain,
    ( ! [X30,X28,X29] :
        ( ~ v3_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X29,u1_struct_0(sK0))
        | ~ m1_subset_1(X30,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X29,X30),X28)
        | r2_hidden(X29,X28)
        | r2_hidden(X30,X28)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f300,f221])).

fof(f300,plain,
    ( ! [X30,X28,X29] :
        ( ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X29,u1_struct_0(sK0))
        | ~ m1_subset_1(X30,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X29,X30),X28)
        | r2_hidden(X29,X28)
        | r2_hidden(X30,X28)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f299,f214])).

fof(f299,plain,
    ( ! [X30,X28,X29] :
        ( ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X29,u1_struct_0(sK0))
        | ~ m1_subset_1(X30,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X29,X30),X28)
        | r2_hidden(X29,X28)
        | r2_hidden(X30,X28)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl19_4
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f262,f207])).

fof(f262,plain,
    ( ! [X30,X28,X29] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X29,u1_struct_0(sK0))
        | ~ m1_subset_1(X30,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X29,X30),X28)
        | r2_hidden(X29,X28)
        | r2_hidden(X30,X28)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f138])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f3697,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k12_lattice3(sK0,sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X1),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ r1_orders_2(sK0,k12_lattice3(sK0,sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X1),sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_25
    | ~ spl19_66
    | ~ spl19_328 ),
    inference(subsumption_resolution,[],[f3613,f3682])).

fof(f3613,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X1),sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ r2_hidden(k12_lattice3(sK0,sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X1),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_25
    | ~ spl19_66 ),
    inference(resolution,[],[f3576,f439])).

fof(f439,plain,
    ( ! [X4,X3] :
        ( r1_orders_2(sK0,k12_lattice3(sK0,X4,X3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f438,f214])).

fof(f438,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X4,X3),X4) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f437,f228])).

fof(f437,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X4,X3),X4) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f432,f221])).

fof(f432,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X4,X3),X4) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | r1_orders_2(sK0,k12_lattice3(sK0,X4,X3),X4) )
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(resolution,[],[f323,f183])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1) ) ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X1)
      | k12_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f3576,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ r1_orders_2(sK0,X0,sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl19_10
    | ~ spl19_25
    | ~ spl19_66 ),
    inference(subsumption_resolution,[],[f3570,f768])).

fof(f3570,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ r1_orders_2(sK0,X0,sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ r1_orders_2(sK0,X0,sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl19_10
    | ~ spl19_25 ),
    inference(resolution,[],[f363,f282])).

fof(f282,plain,
    ( ! [X10,X9] :
        ( v2_waybel_0(X9,sK0)
        | ~ r2_hidden(X10,X9)
        | ~ r1_orders_2(sK0,X10,sK2(sK0,X9))
        | ~ r1_orders_2(sK0,X10,sK3(sK0,X9))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f248,f171])).

fof(f248,plain,
    ( ! [X10,X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r2_hidden(X10,X9)
        | ~ r1_orders_2(sK0,X10,sK2(sK0,X9))
        | ~ r1_orders_2(sK0,X10,sK3(sK0,X9))
        | v2_waybel_0(X9,sK0) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f114])).

fof(f114,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_hidden(X4,X1)
      | ~ r1_orders_2(X0,X4,sK2(X0,X1))
      | ~ r1_orders_2(X0,X4,sK3(X0,X1))
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X4,X3)
                                & r1_orders_2(X0,X4,X2)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',d2_waybel_0)).

fof(f363,plain,
    ( ~ v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_25 ),
    inference(avatar_component_clause,[],[f362])).

fof(f3683,plain,
    ( spl19_328
    | ~ spl19_66
    | ~ spl19_320 ),
    inference(avatar_split_clause,[],[f3658,f3602,f767,f3681])).

fof(f3658,plain,
    ( m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl19_66
    | ~ spl19_320 ),
    inference(resolution,[],[f3608,f768])).

fof(f3608,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(X0))
        | m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0) )
    | ~ spl19_320 ),
    inference(resolution,[],[f3603,f171])).

fof(f3656,plain,
    ( spl19_326
    | ~ spl19_66
    | ~ spl19_68 ),
    inference(avatar_split_clause,[],[f3648,f776,f767,f3654])).

fof(f3648,plain,
    ( m1_subset_1(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl19_66
    | ~ spl19_68 ),
    inference(resolution,[],[f3580,f768])).

fof(f3580,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(X0))
        | m1_subset_1(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0) )
    | ~ spl19_68 ),
    inference(resolution,[],[f777,f171])).

fof(f3604,plain,
    ( spl19_320
    | ~ spl19_10
    | spl19_25
    | ~ spl19_66 ),
    inference(avatar_split_clause,[],[f3575,f767,f362,f227,f3602])).

fof(f3575,plain,
    ( r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_10
    | ~ spl19_25
    | ~ spl19_66 ),
    inference(subsumption_resolution,[],[f3569,f768])).

fof(f3569,plain,
    ( r2_hidden(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_10
    | ~ spl19_25 ),
    inference(resolution,[],[f363,f250])).

fof(f250,plain,
    ( ! [X12] :
        ( v2_waybel_0(X12,sK0)
        | r2_hidden(sK3(sK0,X12),X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK3(X0,X1),X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3451,plain,
    ( ~ spl19_38
    | spl19_45
    | ~ spl19_292 ),
    inference(avatar_contradiction_clause,[],[f3450])).

fof(f3450,plain,
    ( $false
    | ~ spl19_38
    | ~ spl19_45
    | ~ spl19_292 ),
    inference(subsumption_resolution,[],[f3431,f483])).

fof(f483,plain,
    ( ~ r2_hidden(sK14(sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_45 ),
    inference(avatar_component_clause,[],[f482])).

fof(f482,plain,
    ( spl19_45
  <=> ~ r2_hidden(sK14(sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_45])])).

fof(f3431,plain,
    ( r2_hidden(sK14(sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_38
    | ~ spl19_292 ),
    inference(resolution,[],[f3014,f426])).

fof(f426,plain,
    ( m1_subset_1(sK14(sK1),u1_struct_0(sK0))
    | ~ spl19_38 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl19_38
  <=> m1_subset_1(sK14(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_38])])).

fof(f3014,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl19_292 ),
    inference(avatar_component_clause,[],[f3013])).

fof(f3013,plain,
    ( spl19_292
  <=> ! [X2] :
        ( r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_292])])).

fof(f3015,plain,
    ( ~ spl19_291
    | spl19_292
    | spl19_43
    | ~ spl19_66 ),
    inference(avatar_split_clause,[],[f2315,f767,f447,f3013,f3010])).

fof(f447,plain,
    ( spl19_43
  <=> u1_struct_0(sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_43])])).

fof(f2315,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) )
    | ~ spl19_43
    | ~ spl19_66 ),
    inference(resolution,[],[f794,f163])).

fof(f794,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl19_43
    | ~ spl19_66 ),
    inference(subsumption_resolution,[],[f793,f448])).

fof(f448,plain,
    ( u1_struct_0(sK0) != k1_xboole_0
    | ~ spl19_43 ),
    inference(avatar_component_clause,[],[f447])).

fof(f793,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = k1_xboole_0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) )
    | ~ spl19_66 ),
    inference(resolution,[],[f768,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,X0)
      | r2_hidden(X2,X1)
      | r2_hidden(X2,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t50_subset_1)).

fof(f2182,plain,
    ( spl19_204
    | ~ spl19_66
    | ~ spl19_164 ),
    inference(avatar_split_clause,[],[f2155,f1826,f767,f2180])).

fof(f2155,plain,
    ( m1_subset_1(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl19_66
    | ~ spl19_164 ),
    inference(resolution,[],[f1839,f768])).

fof(f1839,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(X0))
        | m1_subset_1(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0) )
    | ~ spl19_164 ),
    inference(resolution,[],[f1827,f171])).

fof(f2110,plain,
    ( ~ spl19_199
    | spl19_200
    | ~ spl19_40
    | spl19_115 ),
    inference(avatar_split_clause,[],[f1191,f1188,f444,f2108,f2102])).

fof(f1188,plain,
    ( spl19_115
  <=> ~ r2_hidden(sK9(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_115])])).

fof(f1191,plain,
    ( r2_hidden(sK9(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl19_40
    | ~ spl19_115 ),
    inference(resolution,[],[f1189,f445])).

fof(f1189,plain,
    ( ~ r2_hidden(sK9(sK0,sK1),sK1)
    | ~ spl19_115 ),
    inference(avatar_component_clause,[],[f1188])).

fof(f2090,plain,
    ( spl19_194
    | ~ spl19_66 ),
    inference(avatar_split_clause,[],[f792,f767,f2088])).

fof(f792,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_66 ),
    inference(resolution,[],[f768,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',d5_subset_1)).

fof(f1828,plain,
    ( spl19_164
    | ~ spl19_10
    | ~ spl19_66
    | spl19_71 ),
    inference(avatar_split_clause,[],[f1749,f800,f767,f227,f1826])).

fof(f1749,plain,
    ( r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_10
    | ~ spl19_66
    | ~ spl19_71 ),
    inference(subsumption_resolution,[],[f1748,f768])).

fof(f1748,plain,
    ( r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_10
    | ~ spl19_71 ),
    inference(resolution,[],[f801,f251])).

fof(f251,plain,
    ( ! [X13] :
        ( v13_waybel_0(X13,sK0)
        | r2_hidden(sK5(sK0,X13),X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK5(X0,X1),X1)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1701,plain,
    ( spl19_1
    | spl19_113
    | ~ spl19_124 ),
    inference(avatar_contradiction_clause,[],[f1700])).

fof(f1700,plain,
    ( $false
    | ~ spl19_1
    | ~ spl19_113
    | ~ spl19_124 ),
    inference(subsumption_resolution,[],[f1688,f1178])).

fof(f1688,plain,
    ( r2_hidden(sK10(sK0,sK1),sK1)
    | ~ spl19_1
    | ~ spl19_124 ),
    inference(resolution,[],[f1302,f244])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl19_1 ),
    inference(resolution,[],[f193,f156])).

fof(f1302,plain,
    ( m1_subset_1(sK10(sK0,sK1),sK1)
    | ~ spl19_124 ),
    inference(avatar_component_clause,[],[f1301])).

fof(f1301,plain,
    ( spl19_124
  <=> m1_subset_1(sK10(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_124])])).

fof(f1608,plain,
    ( u1_struct_0(sK0) != k1_xboole_0
    | ~ r2_hidden(sK14(sK1),u1_struct_0(sK0))
    | r2_hidden(sK14(sK1),k1_xboole_0) ),
    introduced(theory_axiom,[])).

fof(f1607,plain,
    ( spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | spl19_19
    | ~ spl19_94
    | ~ spl19_108
    | spl19_125 ),
    inference(avatar_contradiction_clause,[],[f1606])).

fof(f1606,plain,
    ( $false
    | ~ spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_19
    | ~ spl19_94
    | ~ spl19_108
    | ~ spl19_125 ),
    inference(subsumption_resolution,[],[f1605,f1134])).

fof(f1134,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl19_108 ),
    inference(avatar_component_clause,[],[f1133])).

fof(f1133,plain,
    ( spl19_108
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_108])])).

fof(f1605,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_19
    | ~ spl19_94
    | ~ spl19_125 ),
    inference(subsumption_resolution,[],[f1604,f242])).

fof(f1604,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_19
    | ~ spl19_94
    | ~ spl19_125 ),
    inference(subsumption_resolution,[],[f1603,f235])).

fof(f1603,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_19
    | ~ spl19_94
    | ~ spl19_125 ),
    inference(subsumption_resolution,[],[f1602,f193])).

fof(f1602,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_19
    | ~ spl19_94
    | ~ spl19_125 ),
    inference(subsumption_resolution,[],[f1601,f1305])).

fof(f1305,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1),sK1)
    | ~ spl19_125 ),
    inference(avatar_component_clause,[],[f1304])).

fof(f1304,plain,
    ( spl19_125
  <=> ~ m1_subset_1(sK10(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_125])])).

fof(f1601,plain,
    ( m1_subset_1(sK10(sK0,sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_19
    | ~ spl19_94 ),
    inference(resolution,[],[f1044,f343])).

fof(f1044,plain,
    ( ! [X28] :
        ( v1_waybel_7(X28,sK0)
        | m1_subset_1(sK10(sK0,X28),sK1)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(sK1)) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_94 ),
    inference(forward_demodulation,[],[f1043,f944])).

fof(f944,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl19_94 ),
    inference(avatar_component_clause,[],[f943])).

fof(f943,plain,
    ( spl19_94
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_94])])).

fof(f1043,plain,
    ( ! [X28] :
        ( m1_subset_1(sK10(sK0,X28),sK1)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_waybel_7(X28,sK0) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_94 ),
    inference(subsumption_resolution,[],[f1042,f200])).

fof(f1042,plain,
    ( ! [X28] :
        ( m1_subset_1(sK10(sK0,X28),sK1)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v1_waybel_7(X28,sK0) )
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_94 ),
    inference(subsumption_resolution,[],[f1041,f228])).

fof(f1041,plain,
    ( ! [X28] :
        ( m1_subset_1(sK10(sK0,X28),sK1)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v1_waybel_7(X28,sK0) )
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_94 ),
    inference(subsumption_resolution,[],[f1040,f221])).

fof(f1040,plain,
    ( ! [X28] :
        ( m1_subset_1(sK10(sK0,X28),sK1)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v1_waybel_7(X28,sK0) )
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_94 ),
    inference(subsumption_resolution,[],[f1039,f214])).

fof(f1039,plain,
    ( ! [X28] :
        ( m1_subset_1(sK10(sK0,X28),sK1)
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v1_waybel_7(X28,sK0) )
    | ~ spl19_4
    | ~ spl19_94 ),
    inference(subsumption_resolution,[],[f1005,f207])).

fof(f1005,plain,
    ( ! [X28] :
        ( m1_subset_1(sK10(sK0,X28),sK1)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v1_waybel_7(X28,sK0) )
    | ~ spl19_94 ),
    inference(superposition,[],[f134,f944])).

fof(f1213,plain,
    ( spl19_118
    | spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | spl19_19 ),
    inference(avatar_split_clause,[],[f837,f342,f333,f241,f234,f227,f220,f213,f206,f199,f192,f1211])).

fof(f837,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | ~ spl19_1
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_19 ),
    inference(subsumption_resolution,[],[f836,f193])).

fof(f836,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_19 ),
    inference(subsumption_resolution,[],[f835,f334])).

fof(f835,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_19 ),
    inference(subsumption_resolution,[],[f834,f242])).

fof(f834,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_19 ),
    inference(subsumption_resolution,[],[f831,f235])).

fof(f831,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_19 ),
    inference(resolution,[],[f343,f288])).

fof(f288,plain,
    ( ! [X25] :
        ( v1_waybel_7(X25,sK0)
        | ~ v1_waybel_0(X25,sK0)
        | ~ v12_waybel_0(X25,sK0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k12_lattice3(sK0,sK9(sK0,X25),sK10(sK0,X25)),X25)
        | v1_xboole_0(X25) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f287,f200])).

fof(f287,plain,
    ( ! [X25] :
        ( ~ v3_orders_2(sK0)
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,sK0)
        | ~ v12_waybel_0(X25,sK0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k12_lattice3(sK0,sK9(sK0,X25),sK10(sK0,X25)),X25)
        | v1_waybel_7(X25,sK0) )
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f286,f221])).

fof(f286,plain,
    ( ! [X25] :
        ( ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,sK0)
        | ~ v12_waybel_0(X25,sK0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k12_lattice3(sK0,sK9(sK0,X25),sK10(sK0,X25)),X25)
        | v1_waybel_7(X25,sK0) )
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f285,f214])).

fof(f285,plain,
    ( ! [X25] :
        ( ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,sK0)
        | ~ v12_waybel_0(X25,sK0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k12_lattice3(sK0,sK9(sK0,X25),sK10(sK0,X25)),X25)
        | v1_waybel_7(X25,sK0) )
    | ~ spl19_4
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f259,f207])).

fof(f259,plain,
    ( ! [X25] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X25)
        | ~ v1_waybel_0(X25,sK0)
        | ~ v12_waybel_0(X25,sK0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k12_lattice3(sK0,sK9(sK0,X25),sK10(sK0,X25)),X25)
        | v1_waybel_7(X25,sK0) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k12_lattice3(X0,sK9(X0,X1),sK10(X0,X1)),X1)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1190,plain,
    ( ~ spl19_115
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | spl19_19 ),
    inference(avatar_split_clause,[],[f843,f342,f333,f241,f234,f227,f220,f213,f206,f199,f1188])).

fof(f843,plain,
    ( ~ r2_hidden(sK9(sK0,sK1),sK1)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_19 ),
    inference(subsumption_resolution,[],[f842,f235])).

fof(f842,plain,
    ( ~ r2_hidden(sK9(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_19 ),
    inference(subsumption_resolution,[],[f841,f334])).

fof(f841,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK9(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_19 ),
    inference(subsumption_resolution,[],[f833,f242])).

fof(f833,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK9(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_19 ),
    inference(resolution,[],[f343,f293])).

fof(f293,plain,
    ( ! [X26] :
        ( v1_waybel_7(X26,sK0)
        | ~ v12_waybel_0(X26,sK0)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X26),X26)
        | ~ v1_waybel_0(X26,sK0) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f292,f163])).

fof(f292,plain,
    ( ! [X26] :
        ( v1_xboole_0(X26)
        | ~ v1_waybel_0(X26,sK0)
        | ~ v12_waybel_0(X26,sK0)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X26),X26)
        | v1_waybel_7(X26,sK0) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f291,f200])).

fof(f291,plain,
    ( ! [X26] :
        ( ~ v3_orders_2(sK0)
        | v1_xboole_0(X26)
        | ~ v1_waybel_0(X26,sK0)
        | ~ v12_waybel_0(X26,sK0)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X26),X26)
        | v1_waybel_7(X26,sK0) )
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f290,f221])).

fof(f290,plain,
    ( ! [X26] :
        ( ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X26)
        | ~ v1_waybel_0(X26,sK0)
        | ~ v12_waybel_0(X26,sK0)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X26),X26)
        | v1_waybel_7(X26,sK0) )
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f289,f214])).

fof(f289,plain,
    ( ! [X26] :
        ( ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X26)
        | ~ v1_waybel_0(X26,sK0)
        | ~ v12_waybel_0(X26,sK0)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X26),X26)
        | v1_waybel_7(X26,sK0) )
    | ~ spl19_4
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f260,f207])).

fof(f260,plain,
    ( ! [X26] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X26)
        | ~ v1_waybel_0(X26,sK0)
        | ~ v12_waybel_0(X26,sK0)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X26),X26)
        | v1_waybel_7(X26,sK0) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK9(X0,X1),X1)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1179,plain,
    ( ~ spl19_113
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | spl19_19 ),
    inference(avatar_split_clause,[],[f840,f342,f333,f241,f234,f227,f220,f213,f206,f199,f1177])).

fof(f840,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),sK1)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_12
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_19 ),
    inference(subsumption_resolution,[],[f839,f235])).

fof(f839,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_16
    | ~ spl19_19 ),
    inference(subsumption_resolution,[],[f838,f334])).

fof(f838,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK10(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_14
    | ~ spl19_19 ),
    inference(subsumption_resolution,[],[f832,f242])).

fof(f832,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK10(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10
    | ~ spl19_19 ),
    inference(resolution,[],[f343,f298])).

fof(f298,plain,
    ( ! [X27] :
        ( v1_waybel_7(X27,sK0)
        | ~ v12_waybel_0(X27,sK0)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X27),X27)
        | ~ v1_waybel_0(X27,sK0) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f297,f163])).

fof(f297,plain,
    ( ! [X27] :
        ( v1_xboole_0(X27)
        | ~ v1_waybel_0(X27,sK0)
        | ~ v12_waybel_0(X27,sK0)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X27),X27)
        | v1_waybel_7(X27,sK0) )
    | ~ spl19_2
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f296,f200])).

fof(f296,plain,
    ( ! [X27] :
        ( ~ v3_orders_2(sK0)
        | v1_xboole_0(X27)
        | ~ v1_waybel_0(X27,sK0)
        | ~ v12_waybel_0(X27,sK0)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X27),X27)
        | v1_waybel_7(X27,sK0) )
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_8
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f295,f221])).

fof(f295,plain,
    ( ! [X27] :
        ( ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X27)
        | ~ v1_waybel_0(X27,sK0)
        | ~ v12_waybel_0(X27,sK0)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X27),X27)
        | v1_waybel_7(X27,sK0) )
    | ~ spl19_4
    | ~ spl19_6
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f294,f214])).

fof(f294,plain,
    ( ! [X27] :
        ( ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X27)
        | ~ v1_waybel_0(X27,sK0)
        | ~ v12_waybel_0(X27,sK0)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X27),X27)
        | v1_waybel_7(X27,sK0) )
    | ~ spl19_4
    | ~ spl19_10 ),
    inference(subsumption_resolution,[],[f261,f207])).

fof(f261,plain,
    ( ! [X27] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X27)
        | ~ v1_waybel_0(X27,sK0)
        | ~ v12_waybel_0(X27,sK0)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X27),X27)
        | v1_waybel_7(X27,sK0) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK10(X0,X1),X1)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1135,plain,
    ( spl19_108
    | ~ spl19_16
    | ~ spl19_94 ),
    inference(avatar_split_clause,[],[f965,f943,f333,f1133])).

fof(f965,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl19_16
    | ~ spl19_94 ),
    inference(superposition,[],[f334,f944])).

fof(f945,plain,
    ( spl19_94
    | ~ spl19_84
    | ~ spl19_88 ),
    inference(avatar_split_clause,[],[f938,f910,f887,f943])).

fof(f887,plain,
    ( spl19_84
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_84])])).

fof(f910,plain,
    ( spl19_88
  <=> k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_88])])).

fof(f938,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl19_84
    | ~ spl19_88 ),
    inference(forward_demodulation,[],[f899,f911])).

fof(f911,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = sK1
    | ~ spl19_88 ),
    inference(avatar_component_clause,[],[f910])).

fof(f899,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl19_84 ),
    inference(forward_demodulation,[],[f897,f106])).

fof(f106,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t3_boole)).

fof(f897,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k4_xboole_0(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl19_84 ),
    inference(resolution,[],[f888,f159])).

fof(f888,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_84 ),
    inference(avatar_component_clause,[],[f887])).

fof(f912,plain,
    ( spl19_88
    | ~ spl19_16
    | ~ spl19_20 ),
    inference(avatar_split_clause,[],[f853,f345,f333,f910])).

fof(f345,plain,
    ( spl19_20
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_20])])).

fof(f853,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = sK1
    | ~ spl19_16
    | ~ spl19_20 ),
    inference(subsumption_resolution,[],[f851,f334])).

fof(f851,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_20 ),
    inference(superposition,[],[f158,f346])).

fof(f346,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k1_xboole_0
    | ~ spl19_20 ),
    inference(avatar_component_clause,[],[f345])).

fof(f889,plain,
    ( spl19_84
    | ~ spl19_16
    | ~ spl19_20 ),
    inference(avatar_split_clause,[],[f854,f345,f333,f887])).

fof(f854,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_16
    | ~ spl19_20 ),
    inference(subsumption_resolution,[],[f852,f334])).

fof(f852,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_20 ),
    inference(superposition,[],[f157,f346])).

fof(f157,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',dt_k3_subset_1)).

fof(f823,plain,
    ( spl19_21
    | ~ spl19_72 ),
    inference(avatar_contradiction_clause,[],[f822])).

fof(f822,plain,
    ( $false
    | ~ spl19_21
    | ~ spl19_72 ),
    inference(subsumption_resolution,[],[f821,f349])).

fof(f349,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k1_xboole_0
    | ~ spl19_21 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl19_21
  <=> k3_subset_1(u1_struct_0(sK0),sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_21])])).

fof(f821,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k1_xboole_0
    | ~ spl19_72 ),
    inference(resolution,[],[f807,f131])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t6_boole)).

fof(f807,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_72 ),
    inference(avatar_component_clause,[],[f806])).

fof(f806,plain,
    ( spl19_72
  <=> v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_72])])).

fof(f808,plain,
    ( ~ spl19_71
    | spl19_72
    | ~ spl19_18
    | ~ spl19_24
    | ~ spl19_66 ),
    inference(avatar_split_clause,[],[f795,f767,f365,f339,f806,f800])).

fof(f795,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_18
    | ~ spl19_24
    | ~ spl19_66 ),
    inference(subsumption_resolution,[],[f791,f768])).

fof(f791,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_18
    | ~ spl19_24 ),
    inference(subsumption_resolution,[],[f786,f366])).

fof(f786,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_18 ),
    inference(subsumption_resolution,[],[f94,f340])).

fof(f94,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_7(X1,X0)
          <~> ( k3_subset_1(u1_struct_0(X0),X1) = k1_xboole_0
              | ( m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                & v2_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                & ~ v1_xboole_0(k3_subset_1(u1_struct_0(X0),X1)) ) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_7(X1,X0)
          <~> ( k3_subset_1(u1_struct_0(X0),X1) = k1_xboole_0
              | ( m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                & v2_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                & ~ v1_xboole_0(k3_subset_1(u1_struct_0(X0),X1)) ) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
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
            <=> ( k3_subset_1(u1_struct_0(X0),X1) = k1_xboole_0
                | ( m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
                  & v13_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                  & v2_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                  & ~ v1_xboole_0(k3_subset_1(u1_struct_0(X0),X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
          <=> ( k3_subset_1(u1_struct_0(X0),X1) = k1_xboole_0
              | ( m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                & v2_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                & ~ v1_xboole_0(k3_subset_1(u1_struct_0(X0),X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t22_waybel_7)).

fof(f785,plain,
    ( ~ spl19_16
    | spl19_67 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | ~ spl19_16
    | ~ spl19_67 ),
    inference(subsumption_resolution,[],[f783,f334])).

fof(f783,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_67 ),
    inference(resolution,[],[f771,f157])).

fof(f771,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_67 ),
    inference(avatar_component_clause,[],[f770])).

fof(f770,plain,
    ( spl19_67
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_67])])).

fof(f778,plain,
    ( ~ spl19_67
    | spl19_68
    | ~ spl19_10
    | spl19_25 ),
    inference(avatar_split_clause,[],[f408,f362,f227,f776,f770])).

fof(f408,plain,
    ( r2_hidden(sK2(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl19_10
    | ~ spl19_25 ),
    inference(resolution,[],[f249,f363])).

fof(f249,plain,
    ( ! [X11] :
        ( v2_waybel_0(X11,sK0)
        | r2_hidden(sK2(sK0,X11),X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl19_10 ),
    inference(resolution,[],[f228,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK2(X0,X1),X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f715,plain,
    ( spl19_56
    | spl19_35
    | spl19_37
    | ~ spl19_38 ),
    inference(avatar_split_clause,[],[f708,f425,f417,f405,f713])).

fof(f713,plain,
    ( spl19_56
  <=> r2_hidden(sK14(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_56])])).

fof(f405,plain,
    ( spl19_35
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_35])])).

fof(f417,plain,
    ( spl19_37
  <=> ~ r2_hidden(sK14(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_37])])).

fof(f708,plain,
    ( r2_hidden(sK14(sK1),u1_struct_0(sK0))
    | ~ spl19_35
    | ~ spl19_37
    | ~ spl19_38 ),
    inference(subsumption_resolution,[],[f707,f418])).

fof(f418,plain,
    ( ~ r2_hidden(sK14(sK1),k1_xboole_0)
    | ~ spl19_37 ),
    inference(avatar_component_clause,[],[f417])).

fof(f707,plain,
    ( r2_hidden(sK14(sK1),u1_struct_0(sK0))
    | r2_hidden(sK14(sK1),k1_xboole_0)
    | ~ spl19_35
    | ~ spl19_38 ),
    inference(superposition,[],[f643,f106])).

fof(f643,plain,
    ( ! [X3] :
        ( r2_hidden(sK14(sK1),k4_xboole_0(u1_struct_0(sK0),X3))
        | r2_hidden(sK14(sK1),X3) )
    | ~ spl19_35
    | ~ spl19_38 ),
    inference(resolution,[],[f626,f426])).

fof(f626,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(X2,X3)
        | r2_hidden(X2,k4_xboole_0(u1_struct_0(sK0),X3)) )
    | ~ spl19_35 ),
    inference(resolution,[],[f468,f186])).

fof(f186,plain,(
    ! [X0,X3,X1] :
      ( ~ sP16(X3,X1,X0)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f175])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP16(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f468,plain,
    ( ! [X6,X5] :
        ( sP16(X5,X6,u1_struct_0(sK0))
        | r2_hidden(X5,X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl19_35 ),
    inference(resolution,[],[f409,f172])).

fof(f172,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | sP16(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f409,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl19_35 ),
    inference(resolution,[],[f406,f156])).

fof(f406,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl19_35 ),
    inference(avatar_component_clause,[],[f405])).

fof(f484,plain,
    ( ~ spl19_45
    | ~ spl19_22
    | ~ spl19_28 ),
    inference(avatar_split_clause,[],[f412,f387,f358,f482])).

fof(f358,plain,
    ( spl19_22
  <=> r2_hidden(sK14(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_22])])).

fof(f412,plain,
    ( ~ r2_hidden(sK14(sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl19_22
    | ~ spl19_28 ),
    inference(superposition,[],[f382,f388])).

fof(f382,plain,
    ( ! [X0] : ~ r2_hidden(sK14(sK1),k4_xboole_0(X0,sK1))
    | ~ spl19_22 ),
    inference(resolution,[],[f373,f185])).

fof(f373,plain,
    ( ! [X2] : ~ sP16(sK14(sK1),sK1,X2)
    | ~ spl19_22 ),
    inference(resolution,[],[f359,f174])).

fof(f359,plain,
    ( r2_hidden(sK14(sK1),sK1)
    | ~ spl19_22 ),
    inference(avatar_component_clause,[],[f358])).

fof(f452,plain,
    ( spl19_40
    | spl19_42
    | ~ spl19_16 ),
    inference(avatar_split_clause,[],[f337,f333,f450,f444])).

fof(f450,plain,
    ( spl19_42
  <=> u1_struct_0(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_42])])).

fof(f337,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = k1_xboole_0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl19_16 ),
    inference(resolution,[],[f334,f132])).

fof(f427,plain,
    ( spl19_38
    | ~ spl19_16
    | ~ spl19_22 ),
    inference(avatar_split_clause,[],[f420,f358,f333,f425])).

fof(f420,plain,
    ( m1_subset_1(sK14(sK1),u1_struct_0(sK0))
    | ~ spl19_16
    | ~ spl19_22 ),
    inference(resolution,[],[f371,f334])).

fof(f371,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(sK14(sK1),X0) )
    | ~ spl19_22 ),
    inference(resolution,[],[f359,f171])).

fof(f419,plain,
    ( ~ spl19_37
    | ~ spl19_22 ),
    inference(avatar_split_clause,[],[f411,f358,f417])).

fof(f411,plain,
    ( ~ r2_hidden(sK14(sK1),k1_xboole_0)
    | ~ spl19_22 ),
    inference(superposition,[],[f382,f107])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t4_boole)).

fof(f407,plain,
    ( ~ spl19_35
    | ~ spl19_16
    | ~ spl19_22 ),
    inference(avatar_split_clause,[],[f390,f358,f333,f405])).

fof(f390,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl19_16
    | ~ spl19_22 ),
    inference(resolution,[],[f374,f334])).

fof(f374,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X3))
        | ~ v1_xboole_0(X3) )
    | ~ spl19_22 ),
    inference(resolution,[],[f359,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',t5_subset)).

fof(f389,plain,
    ( spl19_28
    | ~ spl19_16 ),
    inference(avatar_split_clause,[],[f336,f333,f387])).

fof(f336,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl19_16 ),
    inference(resolution,[],[f334,f159])).

fof(f367,plain,
    ( spl19_24
    | spl19_19
    | spl19_21 ),
    inference(avatar_split_clause,[],[f353,f348,f342,f365])).

fof(f353,plain,
    ( v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl19_19
    | ~ spl19_21 ),
    inference(subsumption_resolution,[],[f352,f343])).

fof(f352,plain,
    ( v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl19_21 ),
    inference(subsumption_resolution,[],[f91,f349])).

fof(f91,plain,
    ( v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k1_xboole_0
    | v1_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f360,plain,
    ( spl19_22
    | spl19_1 ),
    inference(avatar_split_clause,[],[f351,f192,f358])).

fof(f351,plain,
    ( r2_hidden(sK14(sK1),sK1)
    | ~ spl19_1 ),
    inference(resolution,[],[f244,f153])).

fof(f153,plain,(
    ! [X0] : m1_subset_1(sK14(X0),X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t22_waybel_7.p',existence_m1_subset_1)).

fof(f350,plain,
    ( ~ spl19_19
    | ~ spl19_21 ),
    inference(avatar_split_clause,[],[f95,f348,f342])).

fof(f95,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k1_xboole_0
    | ~ v1_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f335,plain,(
    spl19_16 ),
    inference(avatar_split_clause,[],[f99,f333])).

fof(f99,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f243,plain,(
    spl19_14 ),
    inference(avatar_split_clause,[],[f98,f241])).

fof(f98,plain,(
    v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f236,plain,(
    spl19_12 ),
    inference(avatar_split_clause,[],[f97,f234])).

fof(f97,plain,(
    v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f229,plain,(
    spl19_10 ),
    inference(avatar_split_clause,[],[f104,f227])).

fof(f104,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f222,plain,(
    spl19_8 ),
    inference(avatar_split_clause,[],[f103,f220])).

fof(f103,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f215,plain,(
    spl19_6 ),
    inference(avatar_split_clause,[],[f102,f213])).

fof(f102,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f208,plain,(
    spl19_4 ),
    inference(avatar_split_clause,[],[f101,f206])).

fof(f101,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f201,plain,(
    spl19_2 ),
    inference(avatar_split_clause,[],[f100,f199])).

fof(f100,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f194,plain,(
    ~ spl19_1 ),
    inference(avatar_split_clause,[],[f96,f192])).

fof(f96,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
