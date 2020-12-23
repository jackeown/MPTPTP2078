%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  231 ( 536 expanded)
%              Number of leaves         :   57 ( 268 expanded)
%              Depth                    :   17
%              Number of atoms          : 1152 (3665 expanded)
%              Number of equality atoms :   65 ( 114 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f570,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f147,f155,f160,f165,f170,f181,f184,f189,f192,f200,f209,f240,f242,f244,f278,f287,f298,f305,f307,f442,f532,f537,f546,f564,f569])).

fof(f569,plain,
    ( ~ spl4_12
    | ~ spl4_10
    | ~ spl4_22
    | spl4_1
    | ~ spl4_38
    | ~ spl4_20
    | ~ spl4_19
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f567,f562,f163,f168,f273,f85,f176,f121,f129])).

fof(f129,plain,
    ( spl4_12
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f121,plain,
    ( spl4_10
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f176,plain,
    ( spl4_22
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f85,plain,
    ( spl4_1
  <=> r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f273,plain,
    ( spl4_38
  <=> m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f168,plain,
    ( spl4_20
  <=> m1_subset_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f163,plain,
    ( spl4_19
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f562,plain,
    ( spl4_76
  <=> r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f567,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_19
    | ~ spl4_76 ),
    inference(forward_demodulation,[],[f566,f164])).

fof(f164,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f163])).

fof(f566,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_19
    | ~ spl4_76 ),
    inference(forward_demodulation,[],[f565,f164])).

fof(f565,plain,
    ( r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_76 ),
    inference(superposition,[],[f563,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f563,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f562])).

fof(f564,plain,
    ( spl4_21
    | ~ spl4_22
    | spl4_8
    | ~ spl4_4
    | spl4_76
    | ~ spl4_20
    | ~ spl4_19
    | ~ spl4_73 ),
    inference(avatar_split_clause,[],[f560,f544,f163,f168,f562,f97,f113,f176,f173])).

fof(f173,plain,
    ( spl4_21
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f113,plain,
    ( spl4_8
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f97,plain,
    ( spl4_4
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f544,plain,
    ( spl4_73
  <=> r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f560,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_19
    | ~ spl4_73 ),
    inference(forward_demodulation,[],[f553,f164])).

% (1963)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f553,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_73 ),
    inference(superposition,[],[f545,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_9)).

fof(f545,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f544])).

fof(f546,plain,
    ( spl4_28
    | spl4_21
    | ~ spl4_22
    | ~ spl4_29
    | ~ spl4_38
    | spl4_73
    | ~ spl4_31
    | ~ spl4_30
    | ~ spl4_19
    | ~ spl4_42
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f542,f535,f302,f163,f227,f230,f544,f273,f224,f176,f173,f221])).

fof(f221,plain,
    ( spl4_28
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f224,plain,
    ( spl4_29
  <=> v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f230,plain,
    ( spl4_31
  <=> m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f227,plain,
    ( spl4_30
  <=> v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f302,plain,
    ( spl4_42
  <=> k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f535,plain,
    ( spl4_72
  <=> r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f542,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_19
    | ~ spl4_42
    | ~ spl4_72 ),
    inference(forward_demodulation,[],[f541,f164])).

fof(f541,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_19
    | ~ spl4_42
    | ~ spl4_72 ),
    inference(forward_demodulation,[],[f540,f164])).

fof(f540,plain,
    ( r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_42
    | ~ spl4_72 ),
    inference(forward_demodulation,[],[f538,f303])).

fof(f303,plain,
    ( k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f302])).

fof(f538,plain,
    ( r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_72 ),
    inference(superposition,[],[f536,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
        & v1_funct_2(X2,X0,u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).

fof(f536,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f535])).

fof(f537,plain,
    ( ~ spl4_7
    | ~ spl4_6
    | ~ spl4_5
    | spl4_8
    | spl4_72
    | ~ spl4_4
    | ~ spl4_71 ),
    inference(avatar_split_clause,[],[f533,f530,f97,f535,f113,f101,f105,f109])).

fof(f109,plain,
    ( spl4_7
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f105,plain,
    ( spl4_6
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f101,plain,
    ( spl4_5
  <=> v3_yellow_6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f530,plain,
    ( spl4_71
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0)))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f533,plain,
    ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))
    | v2_struct_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ spl4_4
    | ~ spl4_71 ),
    inference(resolution,[],[f531,f98])).

fof(f98,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f531,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0)))
        | v2_struct_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0) )
    | ~ spl4_71 ),
    inference(avatar_component_clause,[],[f530])).

fof(f532,plain,
    ( ~ spl4_30
    | ~ spl4_31
    | ~ spl4_29
    | spl4_71
    | ~ spl4_2
    | ~ spl4_61 ),
    inference(avatar_split_clause,[],[f528,f440,f89,f530,f224,f230,f227])).

fof(f89,plain,
    ( spl4_2
  <=> v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f440,plain,
    ( spl4_61
  <=> ! [X1,X0] :
        ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1)))
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ v3_yellow_6(X1,sK0)
        | ~ l1_waybel_0(X1,sK0)
        | ~ v1_funct_1(X0)
        | ~ v5_pre_topc(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f528,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
        | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0)))
        | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0)) )
    | ~ spl4_2
    | ~ spl4_61 ),
    inference(resolution,[],[f441,f90])).

fof(f90,plain,
    ( v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f441,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,sK0,sK0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ v3_yellow_6(X1,sK0)
        | ~ l1_waybel_0(X1,sK0)
        | ~ v1_funct_1(X0)
        | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) )
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f440])).

fof(f442,plain,
    ( ~ spl4_16
    | ~ spl4_15
    | ~ spl4_13
    | ~ spl4_12
    | ~ spl4_11
    | ~ spl4_10
    | ~ spl4_9
    | spl4_61
    | ~ spl4_14
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f435,f163,f137,f440,f117,f121,f125,f129,f133,f141,f145])).

fof(f145,plain,
    ( spl4_16
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f141,plain,
    ( spl4_15
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f133,plain,
    ( spl4_13
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f125,plain,
    ( spl4_11
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f117,plain,
    ( spl4_9
  <=> l1_waybel_9(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f137,plain,
    ( spl4_14
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f435,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1)))
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ l1_waybel_0(X1,sK0)
        | ~ v3_yellow_6(X1,sK0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_9(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_14
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f434,f164])).

fof(f434,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ l1_waybel_0(X1,sK0)
        | ~ v3_yellow_6(X1,sK0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_9(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1)))
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_14
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f433,f164])).

fof(f433,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ v5_pre_topc(X0,sK0,sK0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ l1_waybel_0(X1,sK0)
        | ~ v3_yellow_6(X1,sK0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_9(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1)))
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_14
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f432,f164])).

fof(f432,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ l1_waybel_0(X1,sK0)
        | ~ v3_yellow_6(X1,sK0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_9(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1)))
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f75,f138])).

fof(f138,plain,
    ( v3_orders_2(sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v5_pre_topc(X2,X0,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))
              | ~ v5_pre_topc(X2,X0,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))
              | ~ v5_pre_topc(X2,X0,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X0)
               => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_9)).

fof(f307,plain,
    ( spl4_21
    | ~ spl4_22
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f306,f221,f176,f173])).

fof(f306,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_28 ),
    inference(resolution,[],[f222,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_yellow_0)).

fof(f222,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f221])).

fof(f305,plain,
    ( spl4_28
    | ~ spl4_29
    | ~ spl4_30
    | ~ spl4_31
    | ~ spl4_38
    | spl4_42
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f300,f296,f302,f273,f230,f227,f224,f221])).

fof(f296,plain,
    ( spl4_41
  <=> k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f300,plain,
    ( k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))
    | ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ spl4_41 ),
    inference(superposition,[],[f82,f297])).

fof(f297,plain,
    ( k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f296])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f298,plain,
    ( spl4_41
    | ~ spl4_20
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f294,f285,f168,f296])).

fof(f285,plain,
    ( spl4_39
  <=> ! [X0] :
        ( k11_lattice3(sK0,X0,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),k11_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f294,plain,
    ( k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))
    | ~ spl4_20
    | ~ spl4_39 ),
    inference(resolution,[],[f286,f169])).

fof(f169,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f168])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | k11_lattice3(sK0,X0,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),k11_yellow_6(sK0,sK1)) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f285])).

fof(f287,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8
    | spl4_39
    | ~ spl4_4
    | ~ spl4_25
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f283,f207,f198,f97,f285,f113,f109,f105,f101])).

fof(f198,plain,
    ( spl4_25
  <=> ! [X0] :
        ( m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f207,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f283,plain,
    ( ! [X0] :
        ( k11_lattice3(sK0,X0,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),k11_yellow_6(sK0,sK1))
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ v3_yellow_6(sK1,sK0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | ~ spl4_4
    | ~ spl4_25
    | ~ spl4_26 ),
    inference(resolution,[],[f211,f98])).

fof(f211,plain,
    ( ! [X2,X1] :
        ( ~ l1_waybel_0(X2,sK0)
        | k11_lattice3(sK0,X1,k11_yellow_6(sK0,X2)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X1),k11_yellow_6(sK0,X2))
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ v3_yellow_6(X2,sK0)
        | ~ m1_subset_1(X1,k2_struct_0(sK0)) )
    | ~ spl4_25
    | ~ spl4_26 ),
    inference(resolution,[],[f208,f199])).

fof(f199,plain,
    ( ! [X0] :
        ( m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f198])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f207])).

fof(f278,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_25
    | spl4_38 ),
    inference(avatar_split_clause,[],[f276,f273,f198,f113,f109,f105,f101,f97])).

fof(f276,plain,
    ( v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ spl4_25
    | spl4_38 ),
    inference(resolution,[],[f274,f199])).

fof(f274,plain,
    ( ~ m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f273])).

fof(f244,plain,
    ( ~ spl4_20
    | ~ spl4_24
    | spl4_31 ),
    inference(avatar_split_clause,[],[f243,f230,f187,f168])).

fof(f187,plain,
    ( spl4_24
  <=> ! [X0] :
        ( m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f243,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl4_24
    | spl4_31 ),
    inference(resolution,[],[f231,f188])).

fof(f188,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f187])).

fof(f231,plain,
    ( ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f230])).

fof(f242,plain,
    ( ~ spl4_20
    | ~ spl4_23
    | spl4_30 ),
    inference(avatar_split_clause,[],[f241,f227,f179,f168])).

fof(f179,plain,
    ( spl4_23
  <=> ! [X0] :
        ( v1_funct_2(k4_waybel_1(sK0,X0),k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f241,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl4_23
    | spl4_30 ),
    inference(resolution,[],[f228,f180])).

fof(f180,plain,
    ( ! [X0] :
        ( v1_funct_2(k4_waybel_1(sK0,X0),k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f179])).

fof(f228,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f227])).

fof(f240,plain,
    ( spl4_21
    | ~ spl4_22
    | ~ spl4_20
    | ~ spl4_19
    | spl4_29 ),
    inference(avatar_split_clause,[],[f239,f224,f163,f168,f176,f173])).

fof(f239,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_19
    | spl4_29 ),
    inference(forward_demodulation,[],[f238,f164])).

fof(f238,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_29 ),
    inference(resolution,[],[f225,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).

fof(f225,plain,
    ( ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f224])).

fof(f209,plain,
    ( spl4_21
    | spl4_26
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f205,f163,f117,f207,f173])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1)
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f204,f164])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1)
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f203,f164])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f202,f164])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_9 ),
    inference(resolution,[],[f201,f118])).

fof(f118,plain,
    ( l1_waybel_9(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_9(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k11_lattice3(X1,X2,X0) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f150,f68])).

fof(f68,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f150,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X4) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f149,f77])).

fof(f149,plain,(
    ! [X4,X0,X1] :
      ( k11_lattice3(X0,X1,X4) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f148,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f148,plain,(
    ! [X4,X0,X1] :
      ( k11_lattice3(X0,X1,X4) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f83,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( k11_lattice3(X0,X1,X4) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k4_waybel_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

% (1962)Refutation not found, incomplete strategy% (1962)------------------------------
% (1962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1962)Termination reason: Refutation not found, incomplete strategy

% (1962)Memory used [KB]: 1791
% (1962)Time elapsed: 0.089 s
% (1962)------------------------------
% (1962)------------------------------
fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_1(X0,X1) = X2
                  | ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK3(X0,X1,X2)) != k11_lattice3(X0,X1,sK3(X0,X1,X2))
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X4] :
                      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | k4_waybel_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK3(X0,X1,X2)) != k11_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_1(X0,X1) = X2
                  | ? [X3] :
                      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X4] :
                      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | k4_waybel_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_1(X0,X1) = X2
                  | ? [X3] :
                      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k4_waybel_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_waybel_1)).

fof(f200,plain,
    ( spl4_21
    | ~ spl4_16
    | ~ spl4_15
    | ~ spl4_17
    | spl4_25
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f193,f163,f198,f153,f141,f145,f173])).

fof(f153,plain,
    ( spl4_17
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f193,plain,
    ( ! [X0] :
        ( m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v3_yellow_6(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_19 ),
    inference(superposition,[],[f76,f164])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v3_yellow_6(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_yellow_6)).

fof(f192,plain,
    ( ~ spl4_22
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f190,f173,f125,f176])).

fof(f190,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl4_21 ),
    inference(resolution,[],[f174,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f174,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f173])).

fof(f189,plain,
    ( spl4_21
    | ~ spl4_22
    | spl4_24
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f185,f163,f187,f176,f173])).

fof(f185,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_19 ),
    inference(superposition,[],[f79,f164])).

fof(f184,plain,
    ( ~ spl4_9
    | spl4_22 ),
    inference(avatar_split_clause,[],[f182,f176,f117])).

fof(f182,plain,
    ( ~ l1_waybel_9(sK0)
    | spl4_22 ),
    inference(resolution,[],[f177,f68])).

fof(f177,plain,
    ( ~ l1_orders_2(sK0)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f176])).

fof(f181,plain,
    ( spl4_21
    | ~ spl4_22
    | spl4_23
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f171,f163,f179,f176,f173])).

fof(f171,plain,
    ( ! [X0] :
        ( v1_funct_2(k4_waybel_1(sK0,X0),k2_struct_0(sK0),k2_struct_0(sK0))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_19 ),
    inference(superposition,[],[f78,f164])).

fof(f170,plain,
    ( spl4_20
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f166,f163,f93,f168])).

fof(f93,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f166,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(superposition,[],[f94,f164])).

fof(f94,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f165,plain,
    ( spl4_19
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f161,f158,f163])).

fof(f158,plain,
    ( spl4_18
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f161,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_18 ),
    inference(resolution,[],[f65,f159])).

fof(f159,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f158])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f160,plain,
    ( spl4_18
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f156,f153,f158])).

fof(f156,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f154,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f154,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( spl4_17
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f151,f117,f153])).

fof(f151,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f67,f118])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f147,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f49,f145])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    & v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & v3_yellow_6(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_waybel_9(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
                & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,X1)))
              & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & l1_waybel_0(X1,sK0)
          & v3_yellow_6(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_waybel_9(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,X1)))
            & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & l1_waybel_0(X1,sK0)
        & v3_yellow_6(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,sK1)))
          & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_waybel_0(sK1,sK0)
      & v3_yellow_6(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ~ r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,sK1)))
        & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
      & v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
              & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v3_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_waybel_9(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
              & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v3_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_waybel_9(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v3_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
                 => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
               => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_waybel_9)).

fof(f143,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f50,f141])).

fof(f50,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f139,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f51,f137])).

fof(f51,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f135,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f52,f133])).

fof(f52,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f131,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f53,f129])).

fof(f53,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f127,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f54,f125])).

fof(f54,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f123,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f55,f121])).

fof(f55,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f119,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f115,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f57,f113])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f111,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f58,f109])).

fof(f58,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f59,f105])).

fof(f59,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f60,f101])).

fof(f60,plain,(
    v3_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f61,f97])).

fof(f61,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

% (1968)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f95,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f62,f93])).

fof(f62,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f63,f89])).

fof(f63,plain,(
    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f64,f85])).

fof(f64,plain,(
    ~ r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (1949)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (1959)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (1952)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (1964)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (1955)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (1970)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (1949)Refutation not found, incomplete strategy% (1949)------------------------------
% 0.20/0.49  % (1949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1949)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1949)Memory used [KB]: 10618
% 0.20/0.49  % (1949)Time elapsed: 0.067 s
% 0.20/0.49  % (1949)------------------------------
% 0.20/0.49  % (1949)------------------------------
% 0.20/0.49  % (1962)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (1965)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (1950)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (1961)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (1961)Refutation not found, incomplete strategy% (1961)------------------------------
% 0.20/0.49  % (1961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1961)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1961)Memory used [KB]: 6140
% 0.20/0.49  % (1961)Time elapsed: 0.002 s
% 0.20/0.49  % (1961)------------------------------
% 0.20/0.49  % (1961)------------------------------
% 0.20/0.49  % (1970)Refutation not found, incomplete strategy% (1970)------------------------------
% 0.20/0.49  % (1970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1970)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1970)Memory used [KB]: 10618
% 0.20/0.49  % (1970)Time elapsed: 0.069 s
% 0.20/0.49  % (1970)------------------------------
% 0.20/0.49  % (1970)------------------------------
% 0.20/0.49  % (1958)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (1966)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (1957)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (1967)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (1956)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (1953)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (1960)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (1955)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f570,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f147,f155,f160,f165,f170,f181,f184,f189,f192,f200,f209,f240,f242,f244,f278,f287,f298,f305,f307,f442,f532,f537,f546,f564,f569])).
% 0.20/0.50  fof(f569,plain,(
% 0.20/0.50    ~spl4_12 | ~spl4_10 | ~spl4_22 | spl4_1 | ~spl4_38 | ~spl4_20 | ~spl4_19 | ~spl4_76),
% 0.20/0.50    inference(avatar_split_clause,[],[f567,f562,f163,f168,f273,f85,f176,f121,f129])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    spl4_12 <=> v5_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    spl4_10 <=> v2_lattice3(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    spl4_22 <=> l1_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    spl4_1 <=> r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    spl4_38 <=> m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    spl4_20 <=> m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    spl4_19 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.50  fof(f562,plain,(
% 0.20/0.50    spl4_76 <=> r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 0.20/0.50  fof(f567,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | (~spl4_19 | ~spl4_76)),
% 0.20/0.50    inference(forward_demodulation,[],[f566,f164])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f163])).
% 0.20/0.50  fof(f566,plain,(
% 0.20/0.50    ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | (~spl4_19 | ~spl4_76)),
% 0.20/0.50    inference(forward_demodulation,[],[f565,f164])).
% 0.20/0.50  fof(f565,plain,(
% 0.20/0.50    r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | ~spl4_76),
% 0.20/0.50    inference(superposition,[],[f563,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.20/0.50  fof(f563,plain,(
% 0.20/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~spl4_76),
% 0.20/0.50    inference(avatar_component_clause,[],[f562])).
% 0.20/0.50  fof(f564,plain,(
% 0.20/0.50    spl4_21 | ~spl4_22 | spl4_8 | ~spl4_4 | spl4_76 | ~spl4_20 | ~spl4_19 | ~spl4_73),
% 0.20/0.50    inference(avatar_split_clause,[],[f560,f544,f163,f168,f562,f97,f113,f176,f173])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    spl4_21 <=> v2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    spl4_8 <=> v2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    spl4_4 <=> l1_waybel_0(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.50  fof(f544,plain,(
% 0.20/0.50    spl4_73 <=> r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 0.20/0.50  fof(f560,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | (~spl4_19 | ~spl4_73)),
% 0.20/0.50    inference(forward_demodulation,[],[f553,f164])).
% 0.20/0.50  % (1963)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  fof(f553,plain,(
% 0.20/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_73),
% 0.20/0.50    inference(superposition,[],[f545,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_9)).
% 0.20/0.50  fof(f545,plain,(
% 0.20/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~spl4_73),
% 0.20/0.50    inference(avatar_component_clause,[],[f544])).
% 0.20/0.50  fof(f546,plain,(
% 0.20/0.50    spl4_28 | spl4_21 | ~spl4_22 | ~spl4_29 | ~spl4_38 | spl4_73 | ~spl4_31 | ~spl4_30 | ~spl4_19 | ~spl4_42 | ~spl4_72),
% 0.20/0.50    inference(avatar_split_clause,[],[f542,f535,f302,f163,f227,f230,f544,f273,f224,f176,f173,f221])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    spl4_28 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    spl4_29 <=> v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    spl4_31 <=> m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    spl4_30 <=> v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    spl4_42 <=> k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.20/0.50  fof(f535,plain,(
% 0.20/0.50    spl4_72 <=> r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 0.20/0.50  fof(f542,plain,(
% 0.20/0.50    ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | (~spl4_19 | ~spl4_42 | ~spl4_72)),
% 0.20/0.50    inference(forward_demodulation,[],[f541,f164])).
% 0.20/0.50  fof(f541,plain,(
% 0.20/0.50    ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | (~spl4_19 | ~spl4_42 | ~spl4_72)),
% 0.20/0.50    inference(forward_demodulation,[],[f540,f164])).
% 0.20/0.50  fof(f540,plain,(
% 0.20/0.50    r2_hidden(k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | (~spl4_42 | ~spl4_72)),
% 0.20/0.50    inference(forward_demodulation,[],[f538,f303])).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) | ~spl4_42),
% 0.20/0.50    inference(avatar_component_clause,[],[f302])).
% 0.20/0.50  fof(f538,plain,(
% 0.20/0.50    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~spl4_72),
% 0.20/0.50    inference(superposition,[],[f536,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) & v1_funct_2(X2,X0,u1_struct_0(X1)) & v1_funct_1(X2) & l1_orders_2(X1) & ~v2_struct_0(X1) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).
% 0.20/0.50  fof(f536,plain,(
% 0.20/0.50    r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | ~spl4_72),
% 0.20/0.50    inference(avatar_component_clause,[],[f535])).
% 0.20/0.50  fof(f537,plain,(
% 0.20/0.50    ~spl4_7 | ~spl4_6 | ~spl4_5 | spl4_8 | spl4_72 | ~spl4_4 | ~spl4_71),
% 0.20/0.50    inference(avatar_split_clause,[],[f533,f530,f97,f535,f113,f101,f105,f109])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    spl4_7 <=> v4_orders_2(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    spl4_6 <=> v7_waybel_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    spl4_5 <=> v3_yellow_6(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f530,plain,(
% 0.20/0.50    spl4_71 <=> ! [X0] : (v2_struct_0(X0) | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0))) | ~l1_waybel_0(X0,sK0) | ~v3_yellow_6(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 0.20/0.50  fof(f533,plain,(
% 0.20/0.50    r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) | v2_struct_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | (~spl4_4 | ~spl4_71)),
% 0.20/0.50    inference(resolution,[],[f531,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    l1_waybel_0(sK1,sK0) | ~spl4_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f97])).
% 0.20/0.50  fof(f531,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_waybel_0(X0,sK0) | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0))) | v2_struct_0(X0) | ~v3_yellow_6(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0)) ) | ~spl4_71),
% 0.20/0.50    inference(avatar_component_clause,[],[f530])).
% 0.20/0.50  fof(f532,plain,(
% 0.20/0.50    ~spl4_30 | ~spl4_31 | ~spl4_29 | spl4_71 | ~spl4_2 | ~spl4_61),
% 0.20/0.50    inference(avatar_split_clause,[],[f528,f440,f89,f530,f224,f230,f227])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    spl4_2 <=> v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f440,plain,(
% 0.20/0.50    spl4_61 <=> ! [X1,X0] : (r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1))) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,sK0) | ~l1_waybel_0(X1,sK0) | ~v1_funct_1(X0) | ~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.20/0.50  fof(f528,plain,(
% 0.20/0.50    ( ! [X0] : (v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,X0)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),X0))) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0))) ) | (~spl4_2 | ~spl4_61)),
% 0.20/0.50    inference(resolution,[],[f441,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) | ~spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f89])).
% 0.20/0.50  fof(f441,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v5_pre_topc(X0,sK0,sK0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,sK0) | ~l1_waybel_0(X1,sK0) | ~v1_funct_1(X0) | r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0))) ) | ~spl4_61),
% 0.20/0.50    inference(avatar_component_clause,[],[f440])).
% 0.20/0.50  fof(f442,plain,(
% 0.20/0.50    ~spl4_16 | ~spl4_15 | ~spl4_13 | ~spl4_12 | ~spl4_11 | ~spl4_10 | ~spl4_9 | spl4_61 | ~spl4_14 | ~spl4_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f435,f163,f137,f440,f117,f121,f125,f129,f133,f141,f145])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    spl4_16 <=> v2_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    spl4_15 <=> v8_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    spl4_13 <=> v4_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    spl4_11 <=> v1_lattice3(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    spl4_9 <=> l1_waybel_9(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    spl4_14 <=> v3_orders_2(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.50  fof(f435,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(k2_yellow_6(k2_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1))) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~l1_waybel_0(X1,sK0) | ~v3_yellow_6(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_14 | ~spl4_19)),
% 0.20/0.50    inference(forward_demodulation,[],[f434,f164])).
% 0.20/0.50  fof(f434,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | ~v1_funct_1(X0) | ~l1_waybel_0(X1,sK0) | ~v3_yellow_6(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1))) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_14 | ~spl4_19)),
% 0.20/0.50    inference(forward_demodulation,[],[f433,f164])).
% 0.20/0.50  fof(f433,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~l1_waybel_0(X1,sK0) | ~v3_yellow_6(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1))) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl4_14 | ~spl4_19)),
% 0.20/0.50    inference(forward_demodulation,[],[f432,f164])).
% 0.20/0.50  fof(f432,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v5_pre_topc(X0,sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~l1_waybel_0(X1,sK0) | ~v3_yellow_6(X1,sK0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,X1))) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_14),
% 0.20/0.50    inference(resolution,[],[f75,f138])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    v3_orders_2(sK0) | ~spl4_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f137])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X0) => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_9)).
% 0.20/0.50  fof(f307,plain,(
% 0.20/0.50    spl4_21 | ~spl4_22 | ~spl4_28),
% 0.20/0.50    inference(avatar_split_clause,[],[f306,f221,f176,f173])).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~spl4_28),
% 0.20/0.50    inference(resolution,[],[f222,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_yellow_0)).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    v1_xboole_0(k2_struct_0(sK0)) | ~spl4_28),
% 0.20/0.50    inference(avatar_component_clause,[],[f221])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    spl4_28 | ~spl4_29 | ~spl4_30 | ~spl4_31 | ~spl4_38 | spl4_42 | ~spl4_41),
% 0.20/0.50    inference(avatar_split_clause,[],[f300,f296,f302,f273,f230,f227,f224,f221])).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    spl4_41 <=> k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) | ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | v1_xboole_0(k2_struct_0(sK0)) | ~spl4_41),
% 0.20/0.50    inference(superposition,[],[f82,f297])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) | ~spl4_41),
% 0.20/0.50    inference(avatar_component_clause,[],[f296])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    spl4_41 | ~spl4_20 | ~spl4_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f294,f285,f168,f296])).
% 0.20/0.50  fof(f285,plain,(
% 0.20/0.50    spl4_39 <=> ! [X0] : (k11_lattice3(sK0,X0,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),k11_yellow_6(sK0,sK1)) | ~m1_subset_1(X0,k2_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) | (~spl4_20 | ~spl4_39)),
% 0.20/0.50    inference(resolution,[],[f286,f169])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    m1_subset_1(sK2,k2_struct_0(sK0)) | ~spl4_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f168])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | k11_lattice3(sK0,X0,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),k11_yellow_6(sK0,sK1))) ) | ~spl4_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f285])).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_8 | spl4_39 | ~spl4_4 | ~spl4_25 | ~spl4_26),
% 0.20/0.50    inference(avatar_split_clause,[],[f283,f207,f198,f97,f285,f113,f109,f105,f101])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    spl4_25 <=> ! [X0] : (m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    spl4_26 <=> ! [X1,X0] : (~m1_subset_1(X1,k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    ( ! [X0] : (k11_lattice3(sK0,X0,k11_yellow_6(sK0,sK1)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),k11_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | (~spl4_4 | ~spl4_25 | ~spl4_26)),
% 0.20/0.50    inference(resolution,[],[f211,f98])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~l1_waybel_0(X2,sK0) | k11_lattice3(sK0,X1,k11_yellow_6(sK0,X2)) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X1),k11_yellow_6(sK0,X2)) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~v3_yellow_6(X2,sK0) | ~m1_subset_1(X1,k2_struct_0(sK0))) ) | (~spl4_25 | ~spl4_26)),
% 0.20/0.50    inference(resolution,[],[f208,f199])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0)) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0)) ) | ~spl4_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f198])).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1)) ) | ~spl4_26),
% 0.20/0.50    inference(avatar_component_clause,[],[f207])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_8 | ~spl4_25 | spl4_38),
% 0.20/0.50    inference(avatar_split_clause,[],[f276,f273,f198,f113,f109,f105,f101,f97])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | (~spl4_25 | spl4_38)),
% 0.20/0.50    inference(resolution,[],[f274,f199])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    ~m1_subset_1(k11_yellow_6(sK0,sK1),k2_struct_0(sK0)) | spl4_38),
% 0.20/0.50    inference(avatar_component_clause,[],[f273])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    ~spl4_20 | ~spl4_24 | spl4_31),
% 0.20/0.50    inference(avatar_split_clause,[],[f243,f230,f187,f168])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    spl4_24 <=> ! [X0] : (m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~m1_subset_1(X0,k2_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.50  fof(f243,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl4_24 | spl4_31)),
% 0.20/0.50    inference(resolution,[],[f231,f188])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | ~spl4_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f187])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | spl4_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f230])).
% 0.20/0.50  fof(f242,plain,(
% 0.20/0.50    ~spl4_20 | ~spl4_23 | spl4_30),
% 0.20/0.50    inference(avatar_split_clause,[],[f241,f227,f179,f168])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    spl4_23 <=> ! [X0] : (v1_funct_2(k4_waybel_1(sK0,X0),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl4_23 | spl4_30)),
% 0.20/0.50    inference(resolution,[],[f228,f180])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_2(k4_waybel_1(sK0,X0),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | ~spl4_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f179])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    ~v1_funct_2(k4_waybel_1(sK0,sK2),k2_struct_0(sK0),k2_struct_0(sK0)) | spl4_30),
% 0.20/0.50    inference(avatar_component_clause,[],[f227])).
% 0.20/0.50  fof(f240,plain,(
% 0.20/0.50    spl4_21 | ~spl4_22 | ~spl4_20 | ~spl4_19 | spl4_29),
% 0.20/0.50    inference(avatar_split_clause,[],[f239,f224,f163,f168,f176,f173])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k2_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | (~spl4_19 | spl4_29)),
% 0.20/0.50    inference(forward_demodulation,[],[f238,f164])).
% 0.20/0.50  fof(f238,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl4_29),
% 0.20/0.50    inference(resolution,[],[f225,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    ~v1_funct_1(k4_waybel_1(sK0,sK2)) | spl4_29),
% 0.20/0.50    inference(avatar_component_clause,[],[f224])).
% 0.20/0.50  fof(f209,plain,(
% 0.20/0.50    spl4_21 | spl4_26 | ~spl4_9 | ~spl4_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f205,f163,f117,f207,f173])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1) | ~m1_subset_1(X0,k2_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl4_9 | ~spl4_19)),
% 0.20/0.50    inference(forward_demodulation,[],[f204,f164])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k11_lattice3(sK0,X0,X1) = k3_funct_2(k2_struct_0(sK0),k2_struct_0(sK0),k4_waybel_1(sK0,X0),X1) | ~m1_subset_1(X0,k2_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl4_9 | ~spl4_19)),
% 0.20/0.50    inference(forward_demodulation,[],[f203,f164])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl4_9 | ~spl4_19)),
% 0.20/0.50    inference(forward_demodulation,[],[f202,f164])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X0),X1) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl4_9),
% 0.20/0.50    inference(resolution,[],[f201,f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    l1_waybel_9(sK0) | ~spl4_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f117])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_waybel_9(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k11_lattice3(X1,X2,X0) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X0) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.20/0.50    inference(resolution,[],[f150,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    ( ! [X4,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k11_lattice3(X0,X1,X4) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f149,f77])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X4,X0,X1] : (k11_lattice3(X0,X1,X4) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f148,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ( ! [X4,X0,X1] : (k11_lattice3(X0,X1,X4) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f83,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X4,X0,X1] : (k11_lattice3(X0,X1,X4) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k4_waybel_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f48])).
% 0.20/0.50  % (1962)Refutation not found, incomplete strategy% (1962)------------------------------
% 0.20/0.50  % (1962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1962)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1962)Memory used [KB]: 1791
% 0.20/0.50  % (1962)Time elapsed: 0.089 s
% 0.20/0.50  % (1962)------------------------------
% 0.20/0.50  % (1962)------------------------------
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK3(X0,X1,X2)) != k11_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,sK3(X0,X1,X2)) != k11_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X4) = k11_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(rectify,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k4_waybel_1(X0,X1) = X2 | ? [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) != k11_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | k4_waybel_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_waybel_1)).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    spl4_21 | ~spl4_16 | ~spl4_15 | ~spl4_17 | spl4_25 | ~spl4_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f193,f163,f198,f153,f141,f145,f173])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    spl4_17 <=> l1_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k11_yellow_6(sK0,X0),k2_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v3_yellow_6(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_19),
% 0.20/0.50    inference(superposition,[],[f76,f164])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_yellow_6)).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    ~spl4_22 | ~spl4_11 | ~spl4_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f190,f173,f125,f176])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl4_21),
% 0.20/0.50    inference(resolution,[],[f174,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~spl4_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f173])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    spl4_21 | ~spl4_22 | spl4_24 | ~spl4_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f185,f163,f187,f176,f173])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k4_waybel_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_19),
% 0.20/0.50    inference(superposition,[],[f79,f164])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    ~spl4_9 | spl4_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f182,f176,f117])).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    ~l1_waybel_9(sK0) | spl4_22),
% 0.20/0.50    inference(resolution,[],[f177,f68])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    ~l1_orders_2(sK0) | spl4_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f176])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    spl4_21 | ~spl4_22 | spl4_23 | ~spl4_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f171,f163,f179,f176,f173])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_2(k4_waybel_1(sK0,X0),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_19),
% 0.20/0.50    inference(superposition,[],[f78,f164])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    spl4_20 | ~spl4_3 | ~spl4_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f166,f163,f93,f168])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    spl4_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    m1_subset_1(sK2,k2_struct_0(sK0)) | (~spl4_3 | ~spl4_19)),
% 0.20/0.50    inference(superposition,[],[f94,f164])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f93])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    spl4_19 | ~spl4_18),
% 0.20/0.50    inference(avatar_split_clause,[],[f161,f158,f163])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    spl4_18 <=> l1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_18),
% 0.20/0.50    inference(resolution,[],[f65,f159])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    l1_struct_0(sK0) | ~spl4_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f158])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    spl4_18 | ~spl4_17),
% 0.20/0.50    inference(avatar_split_clause,[],[f156,f153,f158])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    l1_struct_0(sK0) | ~spl4_17),
% 0.20/0.50    inference(resolution,[],[f154,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    l1_pre_topc(sK0) | ~spl4_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f153])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl4_17 | ~spl4_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f151,f117,f153])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    l1_pre_topc(sK0) | ~spl4_9),
% 0.20/0.50    inference(resolution,[],[f67,f118])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_waybel_9(X0) | l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    spl4_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f49,f145])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ((~r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) & v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) & m1_subset_1(sK2,u1_struct_0(sK0))) & l1_waybel_0(sK1,sK0) & v3_yellow_6(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_waybel_9(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f43,f42,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,X1))) & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) & m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_0(X1,sK0) & v3_yellow_6(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,X1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,X1))) & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) & m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_0(X1,sK0) & v3_yellow_6(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,sK1))) & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) & m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_0(sK1,sK0) & v3_yellow_6(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ? [X2] : (~r2_hidden(k12_lattice3(sK0,X2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,X2,sK1))) & v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) & m1_subset_1(X2,u1_struct_0(sK0))) => (~r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) & v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & (l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f14])).
% 0.20/0.50  fof(f14,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_waybel_9)).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    spl4_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f50,f141])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    v8_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    spl4_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f51,f137])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    v3_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    spl4_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f52,f133])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    v4_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    spl4_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f53,f129])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    v5_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    spl4_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f54,f125])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    v1_lattice3(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    spl4_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f55,f121])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    v2_lattice3(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    spl4_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f56,f117])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    l1_waybel_9(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ~spl4_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f57,f113])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl4_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f58,f109])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    v4_orders_2(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    spl4_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f59,f105])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    v7_waybel_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f60,f101])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    v3_yellow_6(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f61,f97])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    l1_waybel_0(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  % (1968)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f62,f93])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f63,f89])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ~spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f64,f85])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ~r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (1955)------------------------------
% 0.20/0.50  % (1955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1955)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (1955)Memory used [KB]: 11129
% 0.20/0.50  % (1955)Time elapsed: 0.087 s
% 0.20/0.50  % (1955)------------------------------
% 0.20/0.50  % (1955)------------------------------
% 0.20/0.51  % (1954)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (1945)Success in time 0.149 s
%------------------------------------------------------------------------------
