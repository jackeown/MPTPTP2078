%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1973+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:59 EST 2020

% Result     : Theorem 10.65s
% Output     : Refutation 11.29s
% Verified   : 
% Statistics : Number of formulae       :  424 ( 936 expanded)
%              Number of leaves         :   65 ( 371 expanded)
%              Depth                    :   20
%              Number of atoms          : 2268 (4298 expanded)
%              Number of equality atoms :   41 ( 121 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f143,f148,f153,f158,f163,f168,f173,f239,f250,f258,f263,f276,f281,f313,f438,f447,f455,f516,f546,f706,f715,f776,f1258,f1259,f2624,f2629,f2714,f2728,f2896,f3426,f3431,f3452,f3528,f3552,f3630,f3842,f3876,f9449,f9525,f10288,f10421,f10552,f10620,f11071,f11083,f11195,f11301,f12751,f13198])).

fof(f13198,plain,
    ( ~ spl17_19
    | spl17_26 ),
    inference(avatar_contradiction_clause,[],[f13197])).

fof(f13197,plain,
    ( $false
    | ~ spl17_19
    | spl17_26 ),
    inference(subsumption_resolution,[],[f12804,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f12804,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl17_19
    | spl17_26 ),
    inference(superposition,[],[f458,f312])).

fof(f312,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl17_19 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl17_19
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_19])])).

fof(f458,plain,
    ( k1_xboole_0 != k4_xboole_0(u1_struct_0(sK0),sK1)
    | spl17_26 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl17_26
  <=> k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_26])])).

fof(f12751,plain,
    ( ~ spl17_15
    | ~ spl17_45
    | ~ spl17_191 ),
    inference(avatar_contradiction_clause,[],[f12750])).

fof(f12750,plain,
    ( $false
    | ~ spl17_15
    | ~ spl17_45
    | ~ spl17_191 ),
    inference(subsumption_resolution,[],[f10764,f3384])).

fof(f3384,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_191 ),
    inference(avatar_component_clause,[],[f3382])).

fof(f3382,plain,
    ( spl17_191
  <=> r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_191])])).

fof(f10764,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_15
    | ~ spl17_45 ),
    inference(superposition,[],[f10707,f280])).

fof(f280,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl17_15 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl17_15
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_15])])).

fof(f10707,plain,
    ( ! [X0] : ~ r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),k4_xboole_0(X0,sK1))
    | ~ spl17_45 ),
    inference(resolution,[],[f10632,f132])).

fof(f132,plain,(
    ! [X0,X3,X1] :
      ( sP16(X3,X1,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( sP16(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f10632,plain,
    ( ! [X2] : ~ sP16(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1,X2)
    | ~ spl17_45 ),
    inference(resolution,[],[f775,f123])).

fof(f123,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ sP16(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f775,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | ~ spl17_45 ),
    inference(avatar_component_clause,[],[f773])).

fof(f773,plain,
    ( spl17_45
  <=> r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_45])])).

fof(f11301,plain,
    ( ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_13
    | ~ spl17_18
    | spl17_41
    | ~ spl17_150
    | ~ spl17_151
    | ~ spl17_168
    | ~ spl17_170
    | spl17_191
    | ~ spl17_418 ),
    inference(avatar_contradiction_clause,[],[f11300])).

fof(f11300,plain,
    ( $false
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_13
    | ~ spl17_18
    | spl17_41
    | ~ spl17_150
    | ~ spl17_151
    | ~ spl17_168
    | ~ spl17_170
    | spl17_191
    | ~ spl17_418 ),
    inference(subsumption_resolution,[],[f11297,f714])).

fof(f714,plain,
    ( ~ r2_hidden(sK9(sK0,sK1),sK1)
    | spl17_41 ),
    inference(avatar_component_clause,[],[f712])).

fof(f712,plain,
    ( spl17_41
  <=> r2_hidden(sK9(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_41])])).

fof(f11297,plain,
    ( r2_hidden(sK9(sK0,sK1),sK1)
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_13
    | ~ spl17_18
    | ~ spl17_150
    | ~ spl17_151
    | ~ spl17_168
    | ~ spl17_170
    | spl17_191
    | ~ spl17_418 ),
    inference(resolution,[],[f11294,f11089])).

fof(f11089,plain,
    ( ! [X3] :
        ( sP16(sK9(sK0,sK1),X3,k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(sK9(sK0,sK1),X3) )
    | ~ spl17_418 ),
    inference(resolution,[],[f11082,f121])).

fof(f121,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | sP16(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f11082,plain,
    ( r2_hidden(sK9(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_418 ),
    inference(avatar_component_clause,[],[f11080])).

fof(f11080,plain,
    ( spl17_418
  <=> r2_hidden(sK9(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_418])])).

fof(f11294,plain,
    ( ! [X6] : ~ sP16(sK9(sK0,sK1),sK1,X6)
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_13
    | ~ spl17_18
    | ~ spl17_150
    | ~ spl17_151
    | ~ spl17_168
    | ~ spl17_170
    | spl17_191 ),
    inference(subsumption_resolution,[],[f11074,f2894])).

fof(f2894,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_168 ),
    inference(avatar_component_clause,[],[f2893])).

fof(f2893,plain,
    ( spl17_168
  <=> m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_168])])).

fof(f11074,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ sP16(sK9(sK0,sK1),sK1,X6) )
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_13
    | ~ spl17_18
    | ~ spl17_150
    | ~ spl17_151
    | ~ spl17_170
    | spl17_191 ),
    inference(subsumption_resolution,[],[f10993,f2934])).

fof(f2934,plain,
    ( r2_hidden(sK10(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_170 ),
    inference(avatar_component_clause,[],[f2933])).

fof(f2933,plain,
    ( spl17_170
  <=> r2_hidden(sK10(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_170])])).

fof(f10993,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK10(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ sP16(sK9(sK0,sK1),sK1,X6) )
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_13
    | ~ spl17_18
    | ~ spl17_150
    | ~ spl17_151
    | spl17_191 ),
    inference(resolution,[],[f10652,f3383])).

fof(f3383,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | spl17_191 ),
    inference(avatar_component_clause,[],[f3382])).

fof(f10652,plain,
    ( ! [X10,X11,X9] :
        ( r2_hidden(k12_lattice3(sK0,X10,X9),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X9,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ sP16(X10,sK1,X11) )
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_13
    | ~ spl17_18
    | ~ spl17_150
    | ~ spl17_151 ),
    inference(resolution,[],[f10641,f321])).

fof(f321,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X4,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ sP16(X4,sK1,X5) )
    | ~ spl17_18 ),
    inference(resolution,[],[f308,f123])).

fof(f308,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl17_18 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl17_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_18])])).

fof(f10641,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(k12_lattice3(sK0,X0,X1),k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_13
    | ~ spl17_150
    | ~ spl17_151 ),
    inference(subsumption_resolution,[],[f10570,f262])).

fof(f262,plain,
    ( v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl17_13 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl17_13
  <=> v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_13])])).

fof(f10570,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(k12_lattice3(sK0,X0,X1),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_150
    | ~ spl17_151 ),
    inference(subsumption_resolution,[],[f9560,f2618])).

fof(f2618,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_150 ),
    inference(avatar_component_clause,[],[f2617])).

fof(f2617,plain,
    ( spl17_150
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_150])])).

fof(f9560,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X1,k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(k12_lattice3(sK0,X0,X1),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_151 ),
    inference(resolution,[],[f2622,f404])).

fof(f404,plain,
    ( ! [X19,X20,X18] :
        ( ~ v13_waybel_0(X18,sK0)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X19,X18)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(k12_lattice3(sK0,X19,X20),X18)
        | ~ v2_waybel_0(X18,sK0) )
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f210,f162])).

fof(f162,plain,
    ( l1_orders_2(sK0)
    | ~ spl17_6 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl17_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).

fof(f210,plain,
    ( ! [X19,X20,X18] :
        ( ~ l1_orders_2(sK0)
        | ~ v13_waybel_0(X18,sK0)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X19,X18)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(k12_lattice3(sK0,X19,X20),X18)
        | ~ v2_waybel_0(X18,sK0) )
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f209,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f209,plain,
    ( ! [X19,X20,X18] :
        ( ~ l1_orders_2(sK0)
        | ~ v13_waybel_0(X18,sK0)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X20,u1_struct_0(sK0))
        | ~ r2_hidden(X19,X18)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(k12_lattice3(sK0,X19,X20),X18)
        | ~ v2_waybel_0(X18,sK0) )
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f208,f120])).

fof(f208,plain,
    ( ! [X19,X20,X18] :
        ( ~ l1_orders_2(sK0)
        | ~ v13_waybel_0(X18,sK0)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ m1_subset_1(X20,u1_struct_0(sK0))
        | ~ r2_hidden(X19,X18)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(k12_lattice3(sK0,X19,X20),X18)
        | ~ v2_waybel_0(X18,sK0) )
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f185,f152])).

fof(f152,plain,
    ( v5_orders_2(sK0)
    | ~ spl17_4 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl17_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f185,plain,
    ( ! [X19,X20,X18] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v13_waybel_0(X18,sK0)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ m1_subset_1(X20,u1_struct_0(sK0))
        | ~ r2_hidden(X19,X18)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(k12_lattice3(sK0,X19,X20),X18)
        | ~ v2_waybel_0(X18,sK0) )
    | ~ spl17_5 ),
    inference(resolution,[],[f157,f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k12_lattice3(X0,X2,X3),X1)
      | ~ v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_waybel_0)).

fof(f157,plain,
    ( v2_lattice3(sK0)
    | ~ spl17_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl17_5
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_5])])).

fof(f2622,plain,
    ( v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl17_151 ),
    inference(avatar_component_clause,[],[f2621])).

fof(f2621,plain,
    ( spl17_151
  <=> v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_151])])).

fof(f11195,plain,
    ( spl17_1
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10
    | spl17_153 ),
    inference(avatar_contradiction_clause,[],[f11194])).

fof(f11194,plain,
    ( $false
    | spl17_1
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10
    | spl17_153 ),
    inference(subsumption_resolution,[],[f11193,f245])).

fof(f245,plain,
    ( ~ v1_waybel_7(sK1,sK0)
    | spl17_10 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl17_10
  <=> v1_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).

fof(f11193,plain,
    ( v1_waybel_7(sK1,sK0)
    | spl17_1
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_153 ),
    inference(subsumption_resolution,[],[f11192,f142])).

fof(f142,plain,
    ( v3_orders_2(sK0)
    | ~ spl17_2 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl17_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f11192,plain,
    ( ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | spl17_1
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_153 ),
    inference(subsumption_resolution,[],[f11191,f238])).

fof(f238,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_9 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl17_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_9])])).

fof(f11191,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | spl17_1
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | spl17_153 ),
    inference(subsumption_resolution,[],[f11190,f172])).

fof(f172,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ spl17_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl17_8
  <=> v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_8])])).

fof(f11190,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | spl17_1
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | spl17_153 ),
    inference(subsumption_resolution,[],[f11189,f167])).

fof(f167,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl17_7 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl17_7
  <=> v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_7])])).

fof(f11189,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | spl17_1
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_153 ),
    inference(subsumption_resolution,[],[f11188,f137])).

fof(f137,plain,
    ( ~ v1_xboole_0(sK1)
    | spl17_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl17_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f11188,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_153 ),
    inference(subsumption_resolution,[],[f11187,f162])).

fof(f11187,plain,
    ( ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | spl17_153 ),
    inference(subsumption_resolution,[],[f11186,f157])).

fof(f11186,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl17_3
    | ~ spl17_4
    | spl17_153 ),
    inference(subsumption_resolution,[],[f11185,f152])).

fof(f11185,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl17_3
    | spl17_153 ),
    inference(subsumption_resolution,[],[f11184,f147])).

fof(f147,plain,
    ( v4_orders_2(sK0)
    | ~ spl17_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl17_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).

fof(f11184,plain,
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
    | spl17_153 ),
    inference(resolution,[],[f2643,f93])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f2643,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | spl17_153 ),
    inference(avatar_component_clause,[],[f2642])).

fof(f2642,plain,
    ( spl17_153
  <=> m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_153])])).

fof(f11083,plain,
    ( ~ spl17_168
    | spl17_418
    | ~ spl17_18
    | spl17_41 ),
    inference(avatar_split_clause,[],[f716,f712,f307,f11080,f2893])).

fof(f716,plain,
    ( r2_hidden(sK9(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_18
    | spl17_41 ),
    inference(resolution,[],[f714,f308])).

fof(f11071,plain,
    ( spl17_1
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10
    | spl17_168 ),
    inference(avatar_contradiction_clause,[],[f11070])).

fof(f11070,plain,
    ( $false
    | spl17_1
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10
    | spl17_168 ),
    inference(subsumption_resolution,[],[f10564,f245])).

fof(f10564,plain,
    ( v1_waybel_7(sK1,sK0)
    | spl17_1
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_168 ),
    inference(subsumption_resolution,[],[f10563,f142])).

fof(f10563,plain,
    ( ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | spl17_1
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_168 ),
    inference(subsumption_resolution,[],[f10562,f238])).

fof(f10562,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | spl17_1
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | spl17_168 ),
    inference(subsumption_resolution,[],[f10561,f172])).

fof(f10561,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | spl17_1
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | spl17_168 ),
    inference(subsumption_resolution,[],[f10560,f167])).

fof(f10560,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | spl17_1
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_168 ),
    inference(subsumption_resolution,[],[f10559,f137])).

fof(f10559,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_168 ),
    inference(subsumption_resolution,[],[f10558,f162])).

fof(f10558,plain,
    ( ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | spl17_168 ),
    inference(subsumption_resolution,[],[f10557,f157])).

fof(f10557,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl17_3
    | ~ spl17_4
    | spl17_168 ),
    inference(subsumption_resolution,[],[f10556,f152])).

fof(f10556,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v1_waybel_7(sK1,sK0)
    | ~ spl17_3
    | spl17_168 ),
    inference(subsumption_resolution,[],[f2897,f147])).

fof(f2897,plain,
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
    | spl17_168 ),
    inference(resolution,[],[f2895,f98])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f2895,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | spl17_168 ),
    inference(avatar_component_clause,[],[f2893])).

fof(f10620,plain,
    ( ~ spl17_18
    | spl17_40
    | ~ spl17_153
    | spl17_170 ),
    inference(avatar_contradiction_clause,[],[f10619])).

fof(f10619,plain,
    ( $false
    | ~ spl17_18
    | spl17_40
    | ~ spl17_153
    | spl17_170 ),
    inference(subsumption_resolution,[],[f10618,f2644])).

fof(f2644,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_153 ),
    inference(avatar_component_clause,[],[f2642])).

fof(f10618,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_18
    | spl17_40
    | spl17_170 ),
    inference(subsumption_resolution,[],[f10614,f2935])).

fof(f2935,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | spl17_170 ),
    inference(avatar_component_clause,[],[f2933])).

fof(f10614,plain,
    ( r2_hidden(sK10(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_18
    | spl17_40 ),
    inference(resolution,[],[f705,f308])).

fof(f705,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),sK1)
    | spl17_40 ),
    inference(avatar_component_clause,[],[f703])).

fof(f703,plain,
    ( spl17_40
  <=> r2_hidden(sK10(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_40])])).

fof(f10552,plain,
    ( ~ spl17_15
    | ~ spl17_203
    | ~ spl17_410 ),
    inference(avatar_contradiction_clause,[],[f10551])).

fof(f10551,plain,
    ( $false
    | ~ spl17_15
    | ~ spl17_203
    | ~ spl17_410 ),
    inference(subsumption_resolution,[],[f10547,f3551])).

fof(f3551,plain,
    ( r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_203 ),
    inference(avatar_component_clause,[],[f3549])).

fof(f3549,plain,
    ( spl17_203
  <=> r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_203])])).

fof(f10547,plain,
    ( ~ r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_15
    | ~ spl17_410 ),
    inference(superposition,[],[f10510,f280])).

fof(f10510,plain,
    ( ! [X0] : ~ r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k4_xboole_0(X0,sK1))
    | ~ spl17_410 ),
    inference(resolution,[],[f10425,f132])).

fof(f10425,plain,
    ( ! [X2] : ~ sP16(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1,X2)
    | ~ spl17_410 ),
    inference(resolution,[],[f10283,f123])).

fof(f10283,plain,
    ( r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl17_410 ),
    inference(avatar_component_clause,[],[f10281])).

fof(f10281,plain,
    ( spl17_410
  <=> r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_410])])).

fof(f10421,plain,
    ( ~ spl17_15
    | ~ spl17_201
    | ~ spl17_411 ),
    inference(avatar_contradiction_clause,[],[f10420])).

fof(f10420,plain,
    ( $false
    | ~ spl17_15
    | ~ spl17_201
    | ~ spl17_411 ),
    inference(subsumption_resolution,[],[f10416,f3527])).

fof(f3527,plain,
    ( r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_201 ),
    inference(avatar_component_clause,[],[f3525])).

fof(f3525,plain,
    ( spl17_201
  <=> r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_201])])).

fof(f10416,plain,
    ( ~ r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_15
    | ~ spl17_411 ),
    inference(superposition,[],[f10371,f280])).

fof(f10371,plain,
    ( ! [X0] : ~ r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k4_xboole_0(X0,sK1))
    | ~ spl17_411 ),
    inference(resolution,[],[f10296,f132])).

fof(f10296,plain,
    ( ! [X2] : ~ sP16(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1,X2)
    | ~ spl17_411 ),
    inference(resolution,[],[f10287,f123])).

fof(f10287,plain,
    ( r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl17_411 ),
    inference(avatar_component_clause,[],[f10285])).

fof(f10285,plain,
    ( spl17_411
  <=> r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_411])])).

fof(f10288,plain,
    ( spl17_410
    | spl17_411
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_10
    | ~ spl17_18
    | spl17_206
    | ~ spl17_218
    | ~ spl17_219 ),
    inference(avatar_split_clause,[],[f9601,f3873,f3839,f3627,f307,f243,f236,f170,f165,f160,f155,f150,f145,f140,f10285,f10281])).

fof(f3627,plain,
    ( spl17_206
  <=> r2_hidden(k12_lattice3(sK0,sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_206])])).

fof(f3839,plain,
    ( spl17_218
  <=> m1_subset_1(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_218])])).

fof(f3873,plain,
    ( spl17_219
  <=> m1_subset_1(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_219])])).

fof(f9601,plain,
    ( r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_10
    | ~ spl17_18
    | spl17_206
    | ~ spl17_218
    | ~ spl17_219 ),
    inference(subsumption_resolution,[],[f9600,f3875])).

fof(f3875,plain,
    ( m1_subset_1(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl17_219 ),
    inference(avatar_component_clause,[],[f3873])).

fof(f9600,plain,
    ( r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_10
    | ~ spl17_18
    | spl17_206
    | ~ spl17_218 ),
    inference(subsumption_resolution,[],[f9594,f3841])).

fof(f3841,plain,
    ( m1_subset_1(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl17_218 ),
    inference(avatar_component_clause,[],[f3839])).

fof(f9594,plain,
    ( ~ m1_subset_1(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_10
    | ~ spl17_18
    | spl17_206 ),
    inference(resolution,[],[f3629,f3673])).

fof(f3673,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k12_lattice3(sK0,X3,X2),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,sK1)
        | r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_10
    | ~ spl17_18 ),
    inference(subsumption_resolution,[],[f3672,f327])).

fof(f327,plain,
    ( ! [X21,X22] :
        ( m1_subset_1(k12_lattice3(sK0,X21,X22),u1_struct_0(sK0))
        | ~ m1_subset_1(X22,u1_struct_0(sK0))
        | ~ m1_subset_1(X21,u1_struct_0(sK0)) )
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f211,f162])).

fof(f211,plain,
    ( ! [X21,X22] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | ~ m1_subset_1(X22,u1_struct_0(sK0))
        | m1_subset_1(k12_lattice3(sK0,X21,X22),u1_struct_0(sK0)) )
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f186,f152])).

fof(f186,plain,
    ( ! [X21,X22] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | ~ m1_subset_1(X22,u1_struct_0(sK0))
        | m1_subset_1(k12_lattice3(sK0,X21,X22),u1_struct_0(sK0)) )
    | ~ spl17_5 ),
    inference(resolution,[],[f157,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f3672,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,sK1)
        | r2_hidden(X2,sK1)
        | r2_hidden(k12_lattice3(sK0,X3,X2),k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(k12_lattice3(sK0,X3,X2),u1_struct_0(sK0)) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_10
    | ~ spl17_18 ),
    inference(resolution,[],[f2611,f308])).

fof(f2611,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f1330,f244])).

fof(f244,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ spl17_10 ),
    inference(avatar_component_clause,[],[f243])).

fof(f1330,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK1)
        | r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ v1_waybel_7(sK1,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9 ),
    inference(subsumption_resolution,[],[f1329,f238])).

fof(f1329,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK1)
        | r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ v1_waybel_7(sK1,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f541,f172])).

fof(f541,plain,
    ( ! [X0,X1] :
        ( ~ v12_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X0,X1),sK1)
        | r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ v1_waybel_7(sK1,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7 ),
    inference(resolution,[],[f452,f167])).

fof(f452,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_waybel_0(X3,sK0)
        | ~ v12_waybel_0(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
        | r2_hidden(X4,X3)
        | r2_hidden(X5,X3)
        | ~ v1_waybel_7(X3,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f201,f162])).

fof(f201,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ v1_waybel_0(X3,sK0)
        | ~ v12_waybel_0(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
        | r2_hidden(X4,X3)
        | r2_hidden(X5,X3)
        | ~ v1_waybel_7(X3,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f200,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f200,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_orders_2(sK0)
        | v1_xboole_0(X3)
        | ~ v1_waybel_0(X3,sK0)
        | ~ v12_waybel_0(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
        | r2_hidden(X4,X3)
        | r2_hidden(X5,X3)
        | ~ v1_waybel_7(X3,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f199,f142])).

fof(f199,plain,
    ( ! [X4,X5,X3] :
        ( ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X3)
        | ~ v1_waybel_0(X3,sK0)
        | ~ v12_waybel_0(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
        | r2_hidden(X4,X3)
        | r2_hidden(X5,X3)
        | ~ v1_waybel_7(X3,sK0) )
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f198,f152])).

fof(f198,plain,
    ( ! [X4,X5,X3] :
        ( ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X3)
        | ~ v1_waybel_0(X3,sK0)
        | ~ v12_waybel_0(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
        | r2_hidden(X4,X3)
        | r2_hidden(X5,X3)
        | ~ v1_waybel_7(X3,sK0) )
    | ~ spl17_3
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f178,f147])).

fof(f178,plain,
    ( ! [X4,X5,X3] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X3)
        | ~ v1_waybel_0(X3,sK0)
        | ~ v12_waybel_0(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,X4,X5),X3)
        | r2_hidden(X4,X3)
        | r2_hidden(X5,X3)
        | ~ v1_waybel_7(X3,sK0) )
    | ~ spl17_5 ),
    inference(resolution,[],[f157,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
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
    inference(cnf_transformation,[],[f36])).

fof(f3629,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
    | spl17_206 ),
    inference(avatar_component_clause,[],[f3627])).

fof(f9525,plain,
    ( ~ spl17_15
    | ~ spl17_158
    | ~ spl17_400 ),
    inference(avatar_contradiction_clause,[],[f9524])).

fof(f9524,plain,
    ( $false
    | ~ spl17_15
    | ~ spl17_158
    | ~ spl17_400 ),
    inference(subsumption_resolution,[],[f9520,f2727])).

fof(f2727,plain,
    ( r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_158 ),
    inference(avatar_component_clause,[],[f2725])).

fof(f2725,plain,
    ( spl17_158
  <=> r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_158])])).

fof(f9520,plain,
    ( ~ r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_15
    | ~ spl17_400 ),
    inference(superposition,[],[f9507,f280])).

fof(f9507,plain,
    ( ! [X0] : ~ r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k4_xboole_0(X0,sK1))
    | ~ spl17_400 ),
    inference(resolution,[],[f9453,f132])).

fof(f9453,plain,
    ( ! [X2] : ~ sP16(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1,X2)
    | ~ spl17_400 ),
    inference(resolution,[],[f9448,f123])).

fof(f9448,plain,
    ( r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl17_400 ),
    inference(avatar_component_clause,[],[f9446])).

fof(f9446,plain,
    ( spl17_400
  <=> r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_400])])).

fof(f9449,plain,
    ( spl17_400
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_150
    | spl17_151
    | ~ spl17_196 ),
    inference(avatar_split_clause,[],[f7551,f3449,f2621,f2617,f236,f170,f160,f9446])).

fof(f3449,plain,
    ( spl17_196
  <=> r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_196])])).

fof(f7551,plain,
    ( r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_150
    | spl17_151
    | ~ spl17_196 ),
    inference(subsumption_resolution,[],[f7550,f3451])).

fof(f3451,plain,
    ( r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl17_196 ),
    inference(avatar_component_clause,[],[f3449])).

fof(f7550,plain,
    ( r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_150
    | spl17_151 ),
    inference(subsumption_resolution,[],[f7546,f2618])).

fof(f7546,plain,
    ( r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_9
    | spl17_151 ),
    inference(resolution,[],[f6403,f2623])).

fof(f2623,plain,
    ( ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl17_151 ),
    inference(avatar_component_clause,[],[f2621])).

fof(f6403,plain,
    ( ! [X0] :
        ( v13_waybel_0(X0,sK0)
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK6(sK0,X0),sK1) )
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_9 ),
    inference(subsumption_resolution,[],[f6397,f162])).

fof(f6397,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK0,X0),sK1)
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v13_waybel_0(X0,sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_9 ),
    inference(duplicate_literal_removal,[],[f6396])).

fof(f6396,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK0,X0),sK1)
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v13_waybel_0(X0,sK0) )
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_9 ),
    inference(resolution,[],[f2678,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f2678,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(sK5(sK0,X6),u1_struct_0(sK0))
        | ~ r2_hidden(sK6(sK0,X6),sK1)
        | r2_hidden(sK5(sK0,X6),sK1)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | v13_waybel_0(X6,sK0) )
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_9 ),
    inference(resolution,[],[f380,f219])).

fof(f219,plain,
    ( ! [X14] :
        ( r1_orders_2(sK0,sK5(sK0,X14),sK6(sK0,X14))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | v13_waybel_0(X14,sK0) )
    | ~ spl17_6 ),
    inference(resolution,[],[f162,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_orders_2(X0,sK5(X0,X1),sK6(X0,X1))
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_9 ),
    inference(subsumption_resolution,[],[f377,f238])).

fof(f377,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(resolution,[],[f234,f172])).

fof(f234,plain,
    ( ! [X24,X23,X22] :
        ( ~ v12_waybel_0(X22,sK0)
        | ~ m1_subset_1(X24,u1_struct_0(sK0))
        | ~ r2_hidden(X23,X22)
        | ~ r1_orders_2(sK0,X24,X23)
        | r2_hidden(X24,X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f225,f120])).

fof(f225,plain,
    ( ! [X24,X23,X22] :
        ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | ~ m1_subset_1(X24,u1_struct_0(sK0))
        | ~ r2_hidden(X23,X22)
        | ~ r1_orders_2(sK0,X24,X23)
        | r2_hidden(X24,X22)
        | ~ v12_waybel_0(X22,sK0) )
    | ~ spl17_6 ),
    inference(resolution,[],[f162,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r2_hidden(X3,X1)
      | ~ v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_waybel_0)).

fof(f3876,plain,
    ( spl17_219
    | ~ spl17_150
    | ~ spl17_203 ),
    inference(avatar_split_clause,[],[f3822,f3549,f2617,f3873])).

fof(f3822,plain,
    ( m1_subset_1(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl17_150
    | ~ spl17_203 ),
    inference(resolution,[],[f3557,f2618])).

fof(f3557,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(X3))
        | m1_subset_1(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X3) )
    | ~ spl17_203 ),
    inference(resolution,[],[f3551,f120])).

fof(f3842,plain,
    ( spl17_218
    | ~ spl17_150
    | ~ spl17_201 ),
    inference(avatar_split_clause,[],[f3819,f3525,f2617,f3839])).

fof(f3819,plain,
    ( m1_subset_1(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl17_150
    | ~ spl17_201 ),
    inference(resolution,[],[f3532,f2618])).

fof(f3532,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(X3))
        | m1_subset_1(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X3) )
    | ~ spl17_201 ),
    inference(resolution,[],[f3527,f120])).

fof(f3630,plain,
    ( ~ spl17_206
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13
    | ~ spl17_150
    | ~ spl17_151 ),
    inference(avatar_split_clause,[],[f3588,f2621,f2617,f260,f160,f155,f150,f3627])).

fof(f3588,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13
    | ~ spl17_150
    | ~ spl17_151 ),
    inference(subsumption_resolution,[],[f3466,f2622])).

fof(f3466,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13
    | ~ spl17_150 ),
    inference(subsumption_resolution,[],[f3460,f2618])).

fof(f3460,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k12_lattice3(sK0,sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13 ),
    inference(resolution,[],[f261,f399])).

fof(f399,plain,
    ( ! [X17] :
        ( v2_waybel_0(X17,sK0)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k12_lattice3(sK0,sK12(sK0,X17),sK13(sK0,X17)),X17)
        | ~ v13_waybel_0(X17,sK0) )
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f207,f162])).

fof(f207,plain,
    ( ! [X17] :
        ( ~ l1_orders_2(sK0)
        | ~ v13_waybel_0(X17,sK0)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k12_lattice3(sK0,sK12(sK0,X17),sK13(sK0,X17)),X17)
        | v2_waybel_0(X17,sK0) )
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f184,f152])).

fof(f184,plain,
    ( ! [X17] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v13_waybel_0(X17,sK0)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k12_lattice3(sK0,sK12(sK0,X17),sK13(sK0,X17)),X17)
        | v2_waybel_0(X17,sK0) )
    | ~ spl17_5 ),
    inference(resolution,[],[f157,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k12_lattice3(X0,sK12(X0,X1),sK13(X0,X1)),X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f261,plain,
    ( ~ v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl17_13 ),
    inference(avatar_component_clause,[],[f260])).

fof(f3552,plain,
    ( spl17_203
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13
    | ~ spl17_150
    | ~ spl17_151 ),
    inference(avatar_split_clause,[],[f3542,f2621,f2617,f260,f160,f155,f150,f3549])).

fof(f3542,plain,
    ( r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13
    | ~ spl17_150
    | ~ spl17_151 ),
    inference(subsumption_resolution,[],[f3465,f2622])).

fof(f3465,plain,
    ( r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13
    | ~ spl17_150 ),
    inference(subsumption_resolution,[],[f3459,f2618])).

fof(f3459,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK13(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13 ),
    inference(resolution,[],[f261,f360])).

fof(f360,plain,
    ( ! [X16] :
        ( v2_waybel_0(X16,sK0)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK13(sK0,X16),X16)
        | ~ v13_waybel_0(X16,sK0) )
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f206,f162])).

fof(f206,plain,
    ( ! [X16] :
        ( ~ l1_orders_2(sK0)
        | ~ v13_waybel_0(X16,sK0)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK13(sK0,X16),X16)
        | v2_waybel_0(X16,sK0) )
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f183,f152])).

fof(f183,plain,
    ( ! [X16] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v13_waybel_0(X16,sK0)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK13(sK0,X16),X16)
        | v2_waybel_0(X16,sK0) )
    | ~ spl17_5 ),
    inference(resolution,[],[f157,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK13(X0,X1),X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3528,plain,
    ( spl17_201
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13
    | ~ spl17_150
    | ~ spl17_151 ),
    inference(avatar_split_clause,[],[f3518,f2621,f2617,f260,f160,f155,f150,f3525])).

fof(f3518,plain,
    ( r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13
    | ~ spl17_150
    | ~ spl17_151 ),
    inference(subsumption_resolution,[],[f3464,f2622])).

fof(f3464,plain,
    ( r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13
    | ~ spl17_150 ),
    inference(subsumption_resolution,[],[f3458,f2618])).

fof(f3458,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK12(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_13 ),
    inference(resolution,[],[f261,f350])).

fof(f350,plain,
    ( ! [X15] :
        ( v2_waybel_0(X15,sK0)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK12(sK0,X15),X15)
        | ~ v13_waybel_0(X15,sK0) )
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f205,f162])).

fof(f205,plain,
    ( ! [X15] :
        ( ~ l1_orders_2(sK0)
        | ~ v13_waybel_0(X15,sK0)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK12(sK0,X15),X15)
        | v2_waybel_0(X15,sK0) )
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f182,f152])).

fof(f182,plain,
    ( ! [X15] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v13_waybel_0(X15,sK0)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK12(sK0,X15),X15)
        | v2_waybel_0(X15,sK0) )
    | ~ spl17_5 ),
    inference(resolution,[],[f157,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK12(X0,X1),X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3452,plain,
    ( spl17_196
    | ~ spl17_194 ),
    inference(avatar_split_clause,[],[f3443,f3420,f3449])).

fof(f3420,plain,
    ( spl17_194
  <=> ! [X0] :
        ( r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0)
        | sP16(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_194])])).

fof(f3443,plain,
    ( r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl17_194 ),
    inference(condensation,[],[f3436])).

fof(f3436,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0)
        | r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) )
    | ~ spl17_194 ),
    inference(resolution,[],[f3421,f122])).

fof(f122,plain,(
    ! [X0,X3,X1] :
      ( ~ sP16(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3421,plain,
    ( ! [X0] :
        ( sP16(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0,sK1)
        | r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0) )
    | ~ spl17_194 ),
    inference(avatar_component_clause,[],[f3420])).

fof(f3431,plain,
    ( ~ spl17_6
    | ~ spl17_150
    | spl17_151
    | spl17_195 ),
    inference(avatar_contradiction_clause,[],[f3430])).

fof(f3430,plain,
    ( $false
    | ~ spl17_6
    | ~ spl17_150
    | spl17_151
    | spl17_195 ),
    inference(subsumption_resolution,[],[f3429,f2623])).

fof(f3429,plain,
    ( v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl17_6
    | ~ spl17_150
    | spl17_195 ),
    inference(subsumption_resolution,[],[f3428,f162])).

fof(f3428,plain,
    ( ~ l1_orders_2(sK0)
    | v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl17_150
    | spl17_195 ),
    inference(subsumption_resolution,[],[f3427,f2618])).

fof(f3427,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl17_195 ),
    inference(resolution,[],[f3425,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3425,plain,
    ( ~ m1_subset_1(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | spl17_195 ),
    inference(avatar_component_clause,[],[f3423])).

fof(f3423,plain,
    ( spl17_195
  <=> m1_subset_1(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_195])])).

fof(f3426,plain,
    ( spl17_194
    | ~ spl17_195
    | ~ spl17_18
    | spl17_156 ),
    inference(avatar_split_clause,[],[f2720,f2711,f307,f3423,f3420])).

fof(f2711,plain,
    ( spl17_156
  <=> r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_156])])).

fof(f2720,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0)
        | sP16(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0,sK1) )
    | ~ spl17_18
    | spl17_156 ),
    inference(resolution,[],[f2713,f320])).

fof(f320,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k3_subset_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(X2,X3)
        | sP16(X2,X3,sK1) )
    | ~ spl17_18 ),
    inference(resolution,[],[f308,f121])).

fof(f2713,plain,
    ( ~ r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | spl17_156 ),
    inference(avatar_component_clause,[],[f2711])).

fof(f2896,plain,
    ( ~ spl17_168
    | ~ spl17_23
    | spl17_41 ),
    inference(avatar_split_clause,[],[f2845,f712,f432,f2893])).

fof(f432,plain,
    ( spl17_23
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_23])])).

fof(f2845,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_23
    | spl17_41 ),
    inference(resolution,[],[f433,f714])).

fof(f433,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl17_23 ),
    inference(avatar_component_clause,[],[f432])).

fof(f2728,plain,
    ( spl17_158
    | ~ spl17_6
    | ~ spl17_150
    | spl17_151 ),
    inference(avatar_split_clause,[],[f2723,f2621,f2617,f160,f2725])).

fof(f2723,plain,
    ( r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_6
    | ~ spl17_150
    | spl17_151 ),
    inference(subsumption_resolution,[],[f2626,f2618])).

fof(f2626,plain,
    ( r2_hidden(sK5(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_6
    | spl17_151 ),
    inference(resolution,[],[f2623,f218])).

fof(f218,plain,
    ( ! [X13] :
        ( v13_waybel_0(X13,sK0)
        | r2_hidden(sK5(sK0,X13),X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_6 ),
    inference(resolution,[],[f162,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK5(X0,X1),X1)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2714,plain,
    ( ~ spl17_156
    | ~ spl17_6
    | ~ spl17_150
    | spl17_151 ),
    inference(avatar_split_clause,[],[f2708,f2621,f2617,f160,f2711])).

fof(f2708,plain,
    ( ~ r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_6
    | ~ spl17_150
    | spl17_151 ),
    inference(subsumption_resolution,[],[f2625,f2618])).

fof(f2625,plain,
    ( ~ r2_hidden(sK6(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_6
    | spl17_151 ),
    inference(resolution,[],[f2623,f220])).

fof(f220,plain,
    ( ! [X15] :
        ( v13_waybel_0(X15,sK0)
        | ~ r2_hidden(sK6(sK0,X15),X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_6 ),
    inference(resolution,[],[f162,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK6(X0,X1),X1)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2629,plain,
    ( ~ spl17_9
    | spl17_150 ),
    inference(avatar_contradiction_clause,[],[f2628])).

fof(f2628,plain,
    ( $false
    | ~ spl17_9
    | spl17_150 ),
    inference(subsumption_resolution,[],[f2627,f238])).

fof(f2627,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl17_150 ),
    inference(resolution,[],[f2619,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f2619,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl17_150 ),
    inference(avatar_component_clause,[],[f2617])).

fof(f2624,plain,
    ( ~ spl17_150
    | ~ spl17_151
    | ~ spl17_10
    | ~ spl17_13
    | spl17_24 ),
    inference(avatar_split_clause,[],[f2615,f435,f260,f243,f2621,f2617])).

fof(f435,plain,
    ( spl17_24
  <=> v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_24])])).

fof(f2615,plain,
    ( ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_10
    | ~ spl17_13
    | spl17_24 ),
    inference(subsumption_resolution,[],[f2613,f437])).

fof(f437,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | spl17_24 ),
    inference(avatar_component_clause,[],[f435])).

fof(f2613,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_10
    | ~ spl17_13 ),
    inference(subsumption_resolution,[],[f2612,f262])).

fof(f2612,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f57,f244])).

fof(f57,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v13_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_7(X1,X0)
          <~> ( k1_xboole_0 = k3_subset_1(u1_struct_0(X0),X1)
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_7(X1,X0)
          <~> ( k1_xboole_0 = k3_subset_1(u1_struct_0(X0),X1)
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
            <=> ( k1_xboole_0 = k3_subset_1(u1_struct_0(X0),X1)
                | ( m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
                  & v13_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                  & v2_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                  & ~ v1_xboole_0(k3_subset_1(u1_struct_0(X0),X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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
          <=> ( k1_xboole_0 = k3_subset_1(u1_struct_0(X0),X1)
              | ( m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                & v2_waybel_0(k3_subset_1(u1_struct_0(X0),X1),X0)
                & ~ v1_xboole_0(k3_subset_1(u1_struct_0(X0),X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_7)).

fof(f1259,plain,
    ( k1_xboole_0 != k4_xboole_0(u1_struct_0(sK0),sK1)
    | k3_subset_1(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1)
    | k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1258,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f776,plain,
    ( spl17_45
    | spl17_1
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10 ),
    inference(avatar_split_clause,[],[f467,f243,f236,f170,f165,f160,f155,f150,f145,f140,f135,f773])).

fof(f467,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | spl17_1
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10 ),
    inference(subsumption_resolution,[],[f466,f137])).

fof(f466,plain,
    ( r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10 ),
    inference(subsumption_resolution,[],[f465,f238])).

fof(f465,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | spl17_10 ),
    inference(subsumption_resolution,[],[f464,f172])).

fof(f464,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | spl17_10 ),
    inference(subsumption_resolution,[],[f461,f167])).

fof(f461,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k12_lattice3(sK0,sK9(sK0,sK1),sK10(sK0,sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_10 ),
    inference(resolution,[],[f245,f424])).

fof(f424,plain,
    ( ! [X0] :
        ( v1_waybel_7(X0,sK0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ v12_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k12_lattice3(sK0,sK9(sK0,X0),sK10(sK0,X0)),X0)
        | v1_xboole_0(X0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f189,f162])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ v12_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k12_lattice3(sK0,sK9(sK0,X0),sK10(sK0,X0)),X0)
        | v1_waybel_7(X0,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f188,f142])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ v12_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k12_lattice3(sK0,sK9(sK0,X0),sK10(sK0,X0)),X0)
        | v1_waybel_7(X0,sK0) )
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f187,f152])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ v12_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k12_lattice3(sK0,sK9(sK0,X0),sK10(sK0,X0)),X0)
        | v1_waybel_7(X0,sK0) )
    | ~ spl17_3
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f175,f147])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ v12_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k12_lattice3(sK0,sK9(sK0,X0),sK10(sK0,X0)),X0)
        | v1_waybel_7(X0,sK0) )
    | ~ spl17_5 ),
    inference(resolution,[],[f157,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k12_lattice3(X0,sK9(X0,X1),sK10(X0,X1)),X1)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f715,plain,
    ( ~ spl17_41
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10 ),
    inference(avatar_split_clause,[],[f473,f243,f236,f170,f165,f160,f155,f150,f145,f140,f712])).

fof(f473,plain,
    ( ~ r2_hidden(sK9(sK0,sK1),sK1)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10 ),
    inference(subsumption_resolution,[],[f472,f167])).

fof(f472,plain,
    ( ~ r2_hidden(sK9(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10 ),
    inference(subsumption_resolution,[],[f471,f238])).

fof(f471,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK9(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_8
    | spl17_10 ),
    inference(subsumption_resolution,[],[f463,f172])).

fof(f463,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK9(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_10 ),
    inference(resolution,[],[f245,f389])).

fof(f389,plain,
    ( ! [X1] :
        ( v1_waybel_7(X1,sK0)
        | ~ v12_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X1),X1)
        | ~ v1_waybel_0(X1,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f193,f162])).

fof(f193,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v1_waybel_0(X1,sK0)
        | ~ v12_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X1),X1)
        | v1_waybel_7(X1,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f192,f118])).

fof(f192,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | v1_xboole_0(X1)
        | ~ v1_waybel_0(X1,sK0)
        | ~ v12_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X1),X1)
        | v1_waybel_7(X1,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f191,f142])).

fof(f191,plain,
    ( ! [X1] :
        ( ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X1)
        | ~ v1_waybel_0(X1,sK0)
        | ~ v12_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X1),X1)
        | v1_waybel_7(X1,sK0) )
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f190,f152])).

fof(f190,plain,
    ( ! [X1] :
        ( ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X1)
        | ~ v1_waybel_0(X1,sK0)
        | ~ v12_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X1),X1)
        | v1_waybel_7(X1,sK0) )
    | ~ spl17_3
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f176,f147])).

fof(f176,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X1)
        | ~ v1_waybel_0(X1,sK0)
        | ~ v12_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK9(sK0,X1),X1)
        | v1_waybel_7(X1,sK0) )
    | ~ spl17_5 ),
    inference(resolution,[],[f157,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK9(X0,X1),X1)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f706,plain,
    ( ~ spl17_40
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10 ),
    inference(avatar_split_clause,[],[f470,f243,f236,f170,f165,f160,f155,f150,f145,f140,f703])).

fof(f470,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),sK1)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10 ),
    inference(subsumption_resolution,[],[f469,f167])).

fof(f469,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_9
    | spl17_10 ),
    inference(subsumption_resolution,[],[f468,f238])).

fof(f468,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK10(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | ~ spl17_8
    | spl17_10 ),
    inference(subsumption_resolution,[],[f462,f172])).

fof(f462,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK10(sK0,sK1),sK1)
    | ~ v1_waybel_0(sK1,sK0)
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6
    | spl17_10 ),
    inference(resolution,[],[f245,f391])).

fof(f391,plain,
    ( ! [X2] :
        ( v1_waybel_7(X2,sK0)
        | ~ v12_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X2),X2)
        | ~ v1_waybel_0(X2,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f197,f162])).

fof(f197,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ v1_waybel_0(X2,sK0)
        | ~ v12_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X2),X2)
        | v1_waybel_7(X2,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f196,f118])).

fof(f196,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | v1_xboole_0(X2)
        | ~ v1_waybel_0(X2,sK0)
        | ~ v12_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X2),X2)
        | v1_waybel_7(X2,sK0) )
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f195,f142])).

fof(f195,plain,
    ( ! [X2] :
        ( ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X2)
        | ~ v1_waybel_0(X2,sK0)
        | ~ v12_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X2),X2)
        | v1_waybel_7(X2,sK0) )
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f194,f152])).

fof(f194,plain,
    ( ! [X2] :
        ( ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X2)
        | ~ v1_waybel_0(X2,sK0)
        | ~ v12_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X2),X2)
        | v1_waybel_7(X2,sK0) )
    | ~ spl17_3
    | ~ spl17_5 ),
    inference(subsumption_resolution,[],[f177,f147])).

fof(f177,plain,
    ( ! [X2] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(X2)
        | ~ v1_waybel_0(X2,sK0)
        | ~ v12_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK10(sK0,X2),X2)
        | v1_waybel_7(X2,sK0) )
    | ~ spl17_5 ),
    inference(resolution,[],[f157,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK10(X0,X1),X1)
      | v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f546,plain,(
    ~ spl17_30 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl17_30 ),
    inference(resolution,[],[f540,f515])).

fof(f515,plain,
    ( r2_hidden(sK14(k1_xboole_0),k1_xboole_0)
    | ~ spl17_30 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl17_30
  <=> r2_hidden(sK14(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_30])])).

fof(f540,plain,
    ( ! [X0] : ~ r2_hidden(sK14(k1_xboole_0),X0)
    | ~ spl17_30 ),
    inference(forward_demodulation,[],[f538,f69])).

fof(f69,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f538,plain,
    ( ! [X0] : ~ r2_hidden(sK14(k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))
    | ~ spl17_30 ),
    inference(resolution,[],[f527,f132])).

fof(f527,plain,
    ( ! [X2] : ~ sP16(sK14(k1_xboole_0),k1_xboole_0,X2)
    | ~ spl17_30 ),
    inference(resolution,[],[f515,f123])).

fof(f516,plain,
    ( spl17_30
    | ~ spl17_11
    | ~ spl17_25 ),
    inference(avatar_split_clause,[],[f487,f444,f247,f513])).

fof(f247,plain,
    ( spl17_11
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_11])])).

fof(f444,plain,
    ( spl17_25
  <=> r2_hidden(sK14(k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_25])])).

fof(f487,plain,
    ( r2_hidden(sK14(k1_xboole_0),k1_xboole_0)
    | ~ spl17_11
    | ~ spl17_25 ),
    inference(forward_demodulation,[],[f446,f248])).

fof(f248,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl17_11 ),
    inference(avatar_component_clause,[],[f247])).

fof(f446,plain,
    ( r2_hidden(sK14(k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_25 ),
    inference(avatar_component_clause,[],[f444])).

fof(f455,plain,
    ( spl17_11
    | ~ spl17_24 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | spl17_11
    | ~ spl17_24 ),
    inference(subsumption_resolution,[],[f453,f249])).

fof(f249,plain,
    ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),sK1)
    | spl17_11 ),
    inference(avatar_component_clause,[],[f247])).

fof(f453,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl17_24 ),
    inference(resolution,[],[f436,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f436,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl17_24 ),
    inference(avatar_component_clause,[],[f435])).

fof(f447,plain,
    ( spl17_25
    | spl17_24 ),
    inference(avatar_split_clause,[],[f441,f435,f444])).

fof(f441,plain,
    ( r2_hidden(sK14(k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | spl17_24 ),
    inference(resolution,[],[f440,f112])).

fof(f112,plain,(
    ! [X0] : m1_subset_1(sK14(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f440,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1)) )
    | spl17_24 ),
    inference(resolution,[],[f437,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f438,plain,
    ( spl17_23
    | ~ spl17_24
    | spl17_14
    | ~ spl17_15 ),
    inference(avatar_split_clause,[],[f426,f278,f273,f435,f432])).

fof(f273,plain,
    ( spl17_14
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_14])])).

fof(f426,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl17_14
    | ~ spl17_15 ),
    inference(superposition,[],[f415,f280])).

fof(f415,plain,
    ( ! [X14,X13] :
        ( ~ v1_xboole_0(k4_xboole_0(u1_struct_0(sK0),X14))
        | r2_hidden(X13,X14)
        | ~ m1_subset_1(X13,u1_struct_0(sK0)) )
    | spl17_14 ),
    inference(resolution,[],[f393,f118])).

fof(f393,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k4_xboole_0(u1_struct_0(sK0),X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(X2,X3) )
    | spl17_14 ),
    inference(resolution,[],[f299,f133])).

fof(f133,plain,(
    ! [X0,X3,X1] :
      ( ~ sP16(X3,X1,X0)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP16(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f299,plain,
    ( ! [X2,X3] :
        ( sP16(X2,X3,u1_struct_0(sK0))
        | r2_hidden(X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl17_14 ),
    inference(resolution,[],[f282,f121])).

fof(f282,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl17_14 ),
    inference(resolution,[],[f275,f114])).

fof(f275,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl17_14 ),
    inference(avatar_component_clause,[],[f273])).

fof(f313,plain,
    ( spl17_18
    | spl17_19
    | ~ spl17_9 ),
    inference(avatar_split_clause,[],[f241,f236,f310,f307])).

fof(f241,plain,
    ( ! [X0] :
        ( k1_xboole_0 = u1_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | r2_hidden(X0,k3_subset_1(u1_struct_0(sK0),sK1)) )
    | ~ spl17_9 ),
    inference(resolution,[],[f238,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,X0)
      | r2_hidden(X2,X1)
      | r2_hidden(X2,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

fof(f281,plain,
    ( spl17_15
    | ~ spl17_9 ),
    inference(avatar_split_clause,[],[f240,f236,f278])).

fof(f240,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl17_9 ),
    inference(resolution,[],[f238,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f276,plain,
    ( ~ spl17_14
    | ~ spl17_9
    | ~ spl17_12 ),
    inference(avatar_split_clause,[],[f271,f255,f236,f273])).

fof(f255,plain,
    ( spl17_12
  <=> r2_hidden(sK14(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_12])])).

fof(f271,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl17_9
    | ~ spl17_12 ),
    inference(resolution,[],[f264,f238])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl17_12 ),
    inference(resolution,[],[f257,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f257,plain,
    ( r2_hidden(sK14(sK1),sK1)
    | ~ spl17_12 ),
    inference(avatar_component_clause,[],[f255])).

fof(f263,plain,
    ( spl17_13
    | spl17_10
    | spl17_11 ),
    inference(avatar_split_clause,[],[f253,f247,f243,f260])).

fof(f253,plain,
    ( v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl17_10
    | spl17_11 ),
    inference(subsumption_resolution,[],[f252,f245])).

fof(f252,plain,
    ( v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v1_waybel_7(sK1,sK0)
    | spl17_11 ),
    inference(subsumption_resolution,[],[f54,f249])).

fof(f54,plain,
    ( v2_waybel_0(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),sK1)
    | v1_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f258,plain,
    ( spl17_12
    | spl17_1 ),
    inference(avatar_split_clause,[],[f251,f135,f255])).

fof(f251,plain,
    ( r2_hidden(sK14(sK1),sK1)
    | spl17_1 ),
    inference(resolution,[],[f174,f112])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(X0,sK1) )
    | spl17_1 ),
    inference(resolution,[],[f137,f114])).

fof(f250,plain,
    ( ~ spl17_10
    | ~ spl17_11 ),
    inference(avatar_split_clause,[],[f58,f247,f243])).

fof(f58,plain,
    ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),sK1)
    | ~ v1_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f239,plain,(
    spl17_9 ),
    inference(avatar_split_clause,[],[f62,f236])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f173,plain,(
    spl17_8 ),
    inference(avatar_split_clause,[],[f61,f170])).

fof(f61,plain,(
    v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f168,plain,(
    spl17_7 ),
    inference(avatar_split_clause,[],[f60,f165])).

fof(f60,plain,(
    v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f163,plain,(
    spl17_6 ),
    inference(avatar_split_clause,[],[f67,f160])).

fof(f67,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f158,plain,(
    spl17_5 ),
    inference(avatar_split_clause,[],[f66,f155])).

fof(f66,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f153,plain,(
    spl17_4 ),
    inference(avatar_split_clause,[],[f65,f150])).

fof(f65,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f148,plain,(
    spl17_3 ),
    inference(avatar_split_clause,[],[f64,f145])).

fof(f64,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f143,plain,(
    spl17_2 ),
    inference(avatar_split_clause,[],[f63,f140])).

fof(f63,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f138,plain,(
    ~ spl17_1 ),
    inference(avatar_split_clause,[],[f59,f135])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

%------------------------------------------------------------------------------
