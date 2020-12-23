%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t39_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:06 EDT 2019

% Result     : Theorem 34.79s
% Output     : Refutation 34.79s
% Verified   : 
% Statistics : Number of formulae       :  391 ( 939 expanded)
%              Number of leaves         :   58 ( 323 expanded)
%              Depth                    :   31
%              Number of atoms          : 2874 (5505 expanded)
%              Number of equality atoms :   38 (  87 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7467,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f198,f205,f212,f219,f226,f233,f240,f247,f254,f362,f369,f376,f383,f406,f410,f441,f474,f511,f520,f555,f848,f861,f878,f2014,f2079,f2084,f2103,f7320,f7346,f7367,f7466])).

fof(f7466,plain,
    ( spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22
    | ~ spl18_74
    | spl18_77
    | ~ spl18_78
    | ~ spl18_178
    | ~ spl18_606
    | ~ spl18_608
    | spl18_611 ),
    inference(avatar_contradiction_clause,[],[f7465])).

fof(f7465,plain,
    ( $false
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22
    | ~ spl18_74
    | ~ spl18_77
    | ~ spl18_78
    | ~ spl18_178
    | ~ spl18_606
    | ~ spl18_608
    | ~ spl18_611 ),
    inference(subsumption_resolution,[],[f7464,f7304])).

fof(f7304,plain,
    ( m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_606 ),
    inference(avatar_component_clause,[],[f7303])).

fof(f7303,plain,
    ( spl18_606
  <=> m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_606])])).

fof(f7464,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22
    | ~ spl18_74
    | ~ spl18_77
    | ~ spl18_78
    | ~ spl18_178
    | ~ spl18_608
    | ~ spl18_611 ),
    inference(subsumption_resolution,[],[f7463,f828])).

fof(f828,plain,
    ( ~ v1_xboole_0(sK7(sK0,sK1))
    | ~ spl18_77 ),
    inference(avatar_component_clause,[],[f827])).

fof(f827,plain,
    ( spl18_77
  <=> ~ v1_xboole_0(sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_77])])).

fof(f7463,plain,
    ( v1_xboole_0(sK7(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22
    | ~ spl18_74
    | ~ spl18_78
    | ~ spl18_178
    | ~ spl18_608
    | ~ spl18_611 ),
    inference(subsumption_resolution,[],[f7462,f7310])).

fof(f7310,plain,
    ( v1_waybel_7(sK7(sK0,sK1),sK0)
    | ~ spl18_608 ),
    inference(avatar_component_clause,[],[f7309])).

fof(f7309,plain,
    ( spl18_608
  <=> v1_waybel_7(sK7(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_608])])).

fof(f7462,plain,
    ( ~ v1_waybel_7(sK7(sK0,sK1),sK0)
    | v1_xboole_0(sK7(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22
    | ~ spl18_74
    | ~ spl18_78
    | ~ spl18_178
    | ~ spl18_611 ),
    inference(subsumption_resolution,[],[f7461,f834])).

fof(f834,plain,
    ( m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl18_78 ),
    inference(avatar_component_clause,[],[f833])).

fof(f833,plain,
    ( spl18_78
  <=> m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_78])])).

fof(f7461,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK7(sK0,sK1),sK0)
    | v1_xboole_0(sK7(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22
    | ~ spl18_74
    | ~ spl18_178
    | ~ spl18_611 ),
    inference(subsumption_resolution,[],[f7460,f822])).

fof(f822,plain,
    ( v1_waybel_0(sK7(sK0,sK1),sK0)
    | ~ spl18_74 ),
    inference(avatar_component_clause,[],[f821])).

fof(f821,plain,
    ( spl18_74
  <=> v1_waybel_0(sK7(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_74])])).

fof(f7460,plain,
    ( ~ v1_waybel_0(sK7(sK0,sK1),sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK7(sK0,sK1),sK0)
    | v1_xboole_0(sK7(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22
    | ~ spl18_178
    | ~ spl18_611 ),
    inference(subsumption_resolution,[],[f7458,f2069])).

fof(f2069,plain,
    ( v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ spl18_178 ),
    inference(avatar_component_clause,[],[f2068])).

fof(f2068,plain,
    ( spl18_178
  <=> v12_waybel_0(sK7(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_178])])).

fof(f7458,plain,
    ( ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ v1_waybel_0(sK7(sK0,sK1),sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK7(sK0,sK1),sK0)
    | v1_xboole_0(sK7(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22
    | ~ spl18_611 ),
    inference(resolution,[],[f7319,f627])).

fof(f627,plain,
    ( ! [X5] :
        ( r2_hidden(sK12(sK0,X5,sK2),sK2)
        | ~ v12_waybel_0(X5,sK0)
        | ~ v1_waybel_0(X5,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_7(X5,sK0)
        | v1_xboole_0(X5)
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),X5) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22 ),
    inference(subsumption_resolution,[],[f626,f375])).

fof(f375,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl18_22 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl18_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_22])])).

fof(f626,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X5,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X5,sK0)
        | r2_hidden(sK12(sK0,X5,sK2),sK2)
        | ~ v1_waybel_7(X5,sK0)
        | v1_xboole_0(X5)
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),X5) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f623,f197])).

fof(f197,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl18_1 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl18_1
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f623,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(sK2)
        | ~ v12_waybel_0(X5,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X5,sK0)
        | r2_hidden(sK12(sK0,X5,sK2),sK2)
        | ~ v1_waybel_7(X5,sK0)
        | v1_xboole_0(X5)
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),X5) )
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(resolution,[],[f544,f204])).

fof(f204,plain,
    ( v1_finset_1(sK2)
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl18_2
  <=> v1_finset_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f544,plain,
    ( ! [X0,X1] :
        ( ~ v1_finset_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | ~ v12_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X0,sK0)
        | r2_hidden(sK12(sK0,X0,X1),X1)
        | ~ v1_waybel_7(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(k2_yellow_0(sK0,X1),X0) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(resolution,[],[f340,f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',t2_subset)).

fof(f340,plain,
    ( ! [X28,X29] :
        ( ~ r2_hidden(k2_yellow_0(sK0,X29),X28)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X29)
        | ~ v1_finset_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X28,sK0)
        | r2_hidden(sK12(sK0,X28,X29),X29)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f339,f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',t7_boole)).

fof(f339,plain,
    ( ! [X28,X29] :
        ( v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X29)
        | ~ v1_finset_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,X29),X28)
        | r2_hidden(sK12(sK0,X28,X29),X29)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f338,f211])).

fof(f211,plain,
    ( v3_orders_2(sK0)
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl18_4
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f338,plain,
    ( ! [X28,X29] :
        ( ~ v3_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X29)
        | ~ v1_finset_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,X29),X28)
        | r2_hidden(sK12(sK0,X28,X29),X29)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f337,f239])).

fof(f239,plain,
    ( v2_lattice3(sK0)
    | ~ spl18_12 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl18_12
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_12])])).

fof(f337,plain,
    ( ! [X28,X29] :
        ( ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X29)
        | ~ v1_finset_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,X29),X28)
        | r2_hidden(sK12(sK0,X28,X29),X29)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f336,f225])).

fof(f225,plain,
    ( v5_orders_2(sK0)
    | ~ spl18_8 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl18_8
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_8])])).

fof(f336,plain,
    ( ! [X28,X29] :
        ( ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X29)
        | ~ v1_finset_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,X29),X28)
        | r2_hidden(sK12(sK0,X28,X29),X29)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl18_6
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f273,f218])).

fof(f218,plain,
    ( v4_orders_2(sK0)
    | ~ spl18_6 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl18_6
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).

fof(f273,plain,
    ( ! [X28,X29] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X28)
        | ~ v1_waybel_0(X28,sK0)
        | ~ v12_waybel_0(X28,sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X29)
        | ~ v1_finset_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,X29),X28)
        | r2_hidden(sK12(sK0,X28,X29),X29)
        | ~ v1_waybel_7(X28,sK0) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_finset_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k2_yellow_0(X0,X2),X1)
      | r2_hidden(sK12(X0,X1,X2),X2)
      | ~ v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r2_hidden(X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v1_finset_1(X2)
                | v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r2_hidden(X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v1_finset_1(X2)
                | v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_finset_1(X2)
                  & ~ v1_xboole_0(X2) )
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( r2_hidden(X3,X1)
                            & r2_hidden(X3,X2) ) )
                    & r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',t16_waybel_7)).

fof(f253,plain,
    ( l1_orders_2(sK0)
    | ~ spl18_16 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl18_16
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_16])])).

fof(f7319,plain,
    ( ~ r2_hidden(sK12(sK0,sK7(sK0,sK1),sK2),sK2)
    | ~ spl18_611 ),
    inference(avatar_component_clause,[],[f7318])).

fof(f7318,plain,
    ( spl18_611
  <=> ~ r2_hidden(sK12(sK0,sK7(sK0,sK1),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_611])])).

fof(f7367,plain,
    ( ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | spl18_609 ),
    inference(avatar_contradiction_clause,[],[f7366])).

fof(f7366,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | ~ spl18_609 ),
    inference(subsumption_resolution,[],[f7365,f361])).

fof(f361,plain,
    ( v4_waybel_7(sK1,sK0)
    | ~ spl18_18 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl18_18
  <=> v4_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_18])])).

fof(f7365,plain,
    ( ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_609 ),
    inference(subsumption_resolution,[],[f7360,f368])).

fof(f368,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl18_20 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl18_20
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_20])])).

fof(f7360,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_609 ),
    inference(resolution,[],[f7313,f304])).

fof(f304,plain,
    ( ! [X19] :
        ( v1_waybel_7(sK7(sK0,X19),sK0)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ v4_waybel_7(X19,sK0) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f303,f211])).

fof(f303,plain,
    ( ! [X19] :
        ( ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | v1_waybel_7(sK7(sK0,X19),sK0)
        | ~ v4_waybel_7(X19,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f302,f239])).

fof(f302,plain,
    ( ! [X19] :
        ( ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | v1_waybel_7(sK7(sK0,X19),sK0)
        | ~ v4_waybel_7(X19,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f301,f232])).

fof(f232,plain,
    ( v1_lattice3(sK0)
    | ~ spl18_10 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl18_10
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_10])])).

fof(f301,plain,
    ( ! [X19] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | v1_waybel_7(sK7(sK0,X19),sK0)
        | ~ v4_waybel_7(X19,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f300,f225])).

fof(f300,plain,
    ( ! [X19] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | v1_waybel_7(sK7(sK0,X19),sK0)
        | ~ v4_waybel_7(X19,sK0) )
    | ~ spl18_6
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f266,f218])).

fof(f266,plain,
    ( ! [X19] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | v1_waybel_7(sK7(sK0,X19),sK0)
        | ~ v4_waybel_7(X19,sK0) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_waybel_7(sK7(X0,X1),X0)
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',d6_waybel_7)).

fof(f7313,plain,
    ( ~ v1_waybel_7(sK7(sK0,sK1),sK0)
    | ~ spl18_609 ),
    inference(avatar_component_clause,[],[f7312])).

fof(f7312,plain,
    ( spl18_609
  <=> ~ v1_waybel_7(sK7(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_609])])).

fof(f7346,plain,
    ( ~ spl18_48
    | ~ spl18_166
    | spl18_607 ),
    inference(avatar_contradiction_clause,[],[f7345])).

fof(f7345,plain,
    ( $false
    | ~ spl18_48
    | ~ spl18_166
    | ~ spl18_607 ),
    inference(subsumption_resolution,[],[f7343,f1985])).

fof(f1985,plain,
    ( m1_subset_1(k1_waybel_3(sK0,sK1),k1_zfmisc_1(sK7(sK0,sK1)))
    | ~ spl18_166 ),
    inference(avatar_component_clause,[],[f1984])).

fof(f1984,plain,
    ( spl18_166
  <=> m1_subset_1(k1_waybel_3(sK0,sK1),k1_zfmisc_1(sK7(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_166])])).

fof(f7343,plain,
    ( ~ m1_subset_1(k1_waybel_3(sK0,sK1),k1_zfmisc_1(sK7(sK0,sK1)))
    | ~ spl18_48
    | ~ spl18_607 ),
    inference(resolution,[],[f7307,f575])).

fof(f575,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_yellow_0(sK0,sK2),X0)
        | ~ m1_subset_1(k1_waybel_3(sK0,sK1),k1_zfmisc_1(X0)) )
    | ~ spl18_48 ),
    inference(resolution,[],[f554,f183])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',t4_subset)).

fof(f554,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK2),k1_waybel_3(sK0,sK1))
    | ~ spl18_48 ),
    inference(avatar_component_clause,[],[f553])).

fof(f553,plain,
    ( spl18_48
  <=> r2_hidden(k2_yellow_0(sK0,sK2),k1_waybel_3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_48])])).

fof(f7307,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_607 ),
    inference(avatar_component_clause,[],[f7306])).

fof(f7306,plain,
    ( spl18_607
  <=> ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_607])])).

fof(f7320,plain,
    ( ~ spl18_607
    | ~ spl18_609
    | ~ spl18_611
    | spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | ~ spl18_22
    | spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_40
    | ~ spl18_74
    | spl18_77
    | ~ spl18_78
    | ~ spl18_166
    | ~ spl18_178 ),
    inference(avatar_split_clause,[],[f4746,f2068,f1984,f833,f827,f821,f503,f472,f425,f401,f374,f367,f360,f252,f238,f231,f224,f217,f210,f203,f196,f7318,f7312,f7306])).

fof(f401,plain,
    ( spl18_29
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_29])])).

fof(f425,plain,
    ( spl18_32
  <=> v24_waybel_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_32])])).

fof(f472,plain,
    ( spl18_38
  <=> k1_yellow_0(sK0,sK7(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_38])])).

fof(f503,plain,
    ( spl18_40
  <=> r2_hidden(k2_yellow_0(sK0,sK2),a_2_0_waybel_3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_40])])).

fof(f4746,plain,
    ( ~ r2_hidden(sK12(sK0,sK7(sK0,sK1),sK2),sK2)
    | ~ v1_waybel_7(sK7(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_40
    | ~ spl18_74
    | ~ spl18_77
    | ~ spl18_78
    | ~ spl18_166
    | ~ spl18_178 ),
    inference(subsumption_resolution,[],[f2086,f4742])).

fof(f4742,plain,
    ( m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_40
    | ~ spl18_77
    | ~ spl18_78
    | ~ spl18_166 ),
    inference(resolution,[],[f3720,f834])).

fof(f3720,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(X1))
        | m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),X1) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_40
    | ~ spl18_77
    | ~ spl18_78
    | ~ spl18_166 ),
    inference(subsumption_resolution,[],[f3719,f361])).

fof(f3719,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(X1))
        | m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),X1)
        | ~ v4_waybel_7(sK1,sK0) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_40
    | ~ spl18_77
    | ~ spl18_78
    | ~ spl18_166 ),
    inference(subsumption_resolution,[],[f3718,f368])).

fof(f3718,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(X1))
        | m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),X1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v4_waybel_7(sK1,sK0) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_40
    | ~ spl18_77
    | ~ spl18_78
    | ~ spl18_166 ),
    inference(subsumption_resolution,[],[f3717,f834])).

fof(f3717,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(X1))
        | m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),X1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v4_waybel_7(sK1,sK0) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_40
    | ~ spl18_77
    | ~ spl18_166 ),
    inference(subsumption_resolution,[],[f3716,f828])).

fof(f3716,plain,
    ( ! [X1] :
        ( v1_xboole_0(sK7(sK0,sK1))
        | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(X1))
        | m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),X1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v4_waybel_7(sK1,sK0) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_40
    | ~ spl18_166 ),
    inference(subsumption_resolution,[],[f3706,f504])).

fof(f504,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK2),a_2_0_waybel_3(sK0,sK1))
    | ~ spl18_40 ),
    inference(avatar_component_clause,[],[f503])).

fof(f3706,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_yellow_0(sK0,sK2),a_2_0_waybel_3(sK0,sK1))
        | v1_xboole_0(sK7(sK0,sK1))
        | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(X1))
        | m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),X1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v4_waybel_7(sK1,sK0) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_166 ),
    inference(resolution,[],[f3425,f1652])).

fof(f1652,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,X5))
        | v1_xboole_0(sK7(sK0,X5))
        | ~ m1_subset_1(sK7(sK0,X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK7(sK0,X5),k1_zfmisc_1(X6))
        | m1_subset_1(sK12(sK0,sK7(sK0,X5),sK2),X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ v4_waybel_7(X5,sK0) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22 ),
    inference(subsumption_resolution,[],[f1651,f299])).

fof(f299,plain,
    ( ! [X18] :
        ( v12_waybel_0(sK7(sK0,X18),sK0)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ v4_waybel_7(X18,sK0) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f298,f211])).

fof(f298,plain,
    ( ! [X18] :
        ( ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | v12_waybel_0(sK7(sK0,X18),sK0)
        | ~ v4_waybel_7(X18,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f297,f239])).

fof(f297,plain,
    ( ! [X18] :
        ( ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | v12_waybel_0(sK7(sK0,X18),sK0)
        | ~ v4_waybel_7(X18,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f296,f232])).

fof(f296,plain,
    ( ! [X18] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | v12_waybel_0(sK7(sK0,X18),sK0)
        | ~ v4_waybel_7(X18,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f295,f225])).

fof(f295,plain,
    ( ! [X18] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | v12_waybel_0(sK7(sK0,X18),sK0)
        | ~ v4_waybel_7(X18,sK0) )
    | ~ spl18_6
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f265,f218])).

fof(f265,plain,
    ( ! [X18] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | v12_waybel_0(sK7(sK0,X18),sK0)
        | ~ v4_waybel_7(X18,sK0) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v12_waybel_0(sK7(X0,X1),X0)
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1651,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(sK7(sK0,X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(sK7(sK0,X5),sK0)
        | v1_xboole_0(sK7(sK0,X5))
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,X5))
        | ~ m1_subset_1(sK7(sK0,X5),k1_zfmisc_1(X6))
        | m1_subset_1(sK12(sK0,sK7(sK0,X5),sK2),X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ v4_waybel_7(X5,sK0) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22 ),
    inference(subsumption_resolution,[],[f1646,f294])).

fof(f294,plain,
    ( ! [X17] :
        ( v1_waybel_0(sK7(sK0,X17),sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ v4_waybel_7(X17,sK0) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f293,f211])).

fof(f293,plain,
    ( ! [X17] :
        ( ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | v1_waybel_0(sK7(sK0,X17),sK0)
        | ~ v4_waybel_7(X17,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f292,f239])).

fof(f292,plain,
    ( ! [X17] :
        ( ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | v1_waybel_0(sK7(sK0,X17),sK0)
        | ~ v4_waybel_7(X17,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f291,f232])).

fof(f291,plain,
    ( ! [X17] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | v1_waybel_0(sK7(sK0,X17),sK0)
        | ~ v4_waybel_7(X17,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f290,f225])).

fof(f290,plain,
    ( ! [X17] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | v1_waybel_0(sK7(sK0,X17),sK0)
        | ~ v4_waybel_7(X17,sK0) )
    | ~ spl18_6
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f264,f218])).

fof(f264,plain,
    ( ! [X17] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | v1_waybel_0(sK7(sK0,X17),sK0)
        | ~ v4_waybel_7(X17,sK0) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_waybel_0(sK7(X0,X1),X0)
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1646,plain,
    ( ! [X6,X5] :
        ( ~ v1_waybel_0(sK7(sK0,X5),sK0)
        | ~ m1_subset_1(sK7(sK0,X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(sK7(sK0,X5),sK0)
        | v1_xboole_0(sK7(sK0,X5))
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,X5))
        | ~ m1_subset_1(sK7(sK0,X5),k1_zfmisc_1(X6))
        | m1_subset_1(sK12(sK0,sK7(sK0,X5),sK2),X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ v4_waybel_7(X5,sK0) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22 ),
    inference(resolution,[],[f732,f304])).

fof(f732,plain,
    ( ! [X0,X1] :
        ( ~ v1_waybel_7(X0,sK0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | m1_subset_1(sK12(sK0,X0,sK2),X1) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22 ),
    inference(resolution,[],[f647,f183])).

fof(f647,plain,
    ( ! [X5] :
        ( r2_hidden(sK12(sK0,X5,sK2),X5)
        | ~ v12_waybel_0(X5,sK0)
        | ~ v1_waybel_0(X5,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_7(X5,sK0)
        | v1_xboole_0(X5)
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),X5) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_22 ),
    inference(subsumption_resolution,[],[f646,f375])).

fof(f646,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X5,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X5,sK0)
        | r2_hidden(sK12(sK0,X5,sK2),X5)
        | ~ v1_waybel_7(X5,sK0)
        | v1_xboole_0(X5)
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),X5) )
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f643,f197])).

fof(f643,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(sK2)
        | ~ v12_waybel_0(X5,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X5,sK0)
        | r2_hidden(sK12(sK0,X5,sK2),X5)
        | ~ v1_waybel_7(X5,sK0)
        | v1_xboole_0(X5)
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),X5) )
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(resolution,[],[f556,f204])).

fof(f556,plain,
    ( ! [X0,X1] :
        ( ~ v1_finset_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | ~ v12_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X0,sK0)
        | r2_hidden(sK12(sK0,X0,X1),X0)
        | ~ v1_waybel_7(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(k2_yellow_0(sK0,X1),X0) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(resolution,[],[f345,f168])).

fof(f345,plain,
    ( ! [X30,X31] :
        ( ~ r2_hidden(k2_yellow_0(sK0,X31),X30)
        | ~ v12_waybel_0(X30,sK0)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X31)
        | ~ v1_finset_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X30,sK0)
        | r2_hidden(sK12(sK0,X30,X31),X30)
        | ~ v1_waybel_7(X30,sK0) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f344,f175])).

fof(f344,plain,
    ( ! [X30,X31] :
        ( v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,sK0)
        | ~ v12_waybel_0(X30,sK0)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X31)
        | ~ v1_finset_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,X31),X30)
        | r2_hidden(sK12(sK0,X30,X31),X30)
        | ~ v1_waybel_7(X30,sK0) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f343,f211])).

fof(f343,plain,
    ( ! [X30,X31] :
        ( ~ v3_orders_2(sK0)
        | v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,sK0)
        | ~ v12_waybel_0(X30,sK0)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X31)
        | ~ v1_finset_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,X31),X30)
        | r2_hidden(sK12(sK0,X30,X31),X30)
        | ~ v1_waybel_7(X30,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f342,f239])).

fof(f342,plain,
    ( ! [X30,X31] :
        ( ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,sK0)
        | ~ v12_waybel_0(X30,sK0)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X31)
        | ~ v1_finset_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,X31),X30)
        | r2_hidden(sK12(sK0,X30,X31),X30)
        | ~ v1_waybel_7(X30,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f341,f225])).

fof(f341,plain,
    ( ! [X30,X31] :
        ( ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,sK0)
        | ~ v12_waybel_0(X30,sK0)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X31)
        | ~ v1_finset_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,X31),X30)
        | r2_hidden(sK12(sK0,X30,X31),X30)
        | ~ v1_waybel_7(X30,sK0) )
    | ~ spl18_6
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f274,f218])).

fof(f274,plain,
    ( ! [X30,X31] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X30)
        | ~ v1_waybel_0(X30,sK0)
        | ~ v12_waybel_0(X30,sK0)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X31)
        | ~ v1_finset_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,X31),X30)
        | r2_hidden(sK12(sK0,X30,X31),X30)
        | ~ v1_waybel_7(X30,sK0) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_finset_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k2_yellow_0(X0,X2),X1)
      | r2_hidden(sK12(X0,X1,X2),X1)
      | ~ v1_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f3425,plain,
    ( ! [X5] :
        ( m1_subset_1(X5,sK7(sK0,sK1))
        | ~ r2_hidden(X5,a_2_0_waybel_3(sK0,sK1)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_29
    | ~ spl18_166 ),
    inference(subsumption_resolution,[],[f3421,f368])).

fof(f3421,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,a_2_0_waybel_3(sK0,sK1))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | m1_subset_1(X5,sK7(sK0,sK1)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_166 ),
    inference(resolution,[],[f807,f1985])).

fof(f807,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_waybel_3(sK0,X0),k1_zfmisc_1(X2))
        | ~ r2_hidden(X1,a_2_0_waybel_3(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(X1,X2) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(resolution,[],[f796,f183])).

fof(f796,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_waybel_3(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_0_waybel_3(sK0,X1)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(duplicate_literal_removal,[],[f795])).

fof(f795,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_waybel_3(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_0_waybel_3(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_0_waybel_3(sK0,X1)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(superposition,[],[f660,f415])).

fof(f415,plain,
    ( ! [X39,X38] :
        ( sK15(X39,sK0,X38) = X39
        | ~ m1_subset_1(X38,u1_struct_0(sK0))
        | ~ r2_hidden(X39,a_2_0_waybel_3(sK0,X38)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(subsumption_resolution,[],[f352,f402])).

fof(f402,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl18_29 ),
    inference(avatar_component_clause,[],[f401])).

fof(f352,plain,
    ( ! [X39,X38] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X38,u1_struct_0(sK0))
        | sK15(X39,sK0,X38) = X39
        | ~ r2_hidden(X39,a_2_0_waybel_3(sK0,X38)) )
    | ~ spl18_4
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f279,f211])).

fof(f279,plain,
    ( ! [X39,X38] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X38,u1_struct_0(sK0))
        | sK15(X39,sK0,X38) = X39
        | ~ r2_hidden(X39,a_2_0_waybel_3(sK0,X38)) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sK15(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',fraenkel_a_2_0_waybel_3)).

fof(f660,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK15(X1,sK0,X0),k1_waybel_3(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_0_waybel_3(sK0,X0)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(duplicate_literal_removal,[],[f659])).

fof(f659,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK15(X1,sK0,X0),k1_waybel_3(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_0_waybel_3(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(superposition,[],[f598,f412])).

fof(f412,plain,
    ( ! [X8] :
        ( k1_waybel_3(sK0,X8) = a_2_0_waybel_3(sK0,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(subsumption_resolution,[],[f285,f402])).

fof(f285,plain,
    ( ! [X8] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | k1_waybel_3(sK0,X8) = a_2_0_waybel_3(sK0,X8) )
    | ~ spl18_4
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f259,f211])).

fof(f259,plain,
    ( ! [X8] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | k1_waybel_3(sK0,X8) = a_2_0_waybel_3(sK0,X8) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',d3_waybel_3)).

fof(f598,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK15(X1,sK0,X0),a_2_0_waybel_3(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_0_waybel_3(sK0,X0)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(subsumption_resolution,[],[f597,f402])).

fof(f597,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK15(X1,sK0,X0),a_2_0_waybel_3(sK0,X0))
        | ~ r2_hidden(X1,a_2_0_waybel_3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(subsumption_resolution,[],[f596,f253])).

fof(f596,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK15(X1,sK0,X0),a_2_0_waybel_3(sK0,X0))
        | ~ r2_hidden(X1,a_2_0_waybel_3(sK0,X0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(subsumption_resolution,[],[f595,f211])).

fof(f595,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK15(X1,sK0,X0),a_2_0_waybel_3(sK0,X0))
        | ~ r2_hidden(X1,a_2_0_waybel_3(sK0,X0))
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(duplicate_literal_removal,[],[f591])).

fof(f591,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK15(X1,sK0,X0),a_2_0_waybel_3(sK0,X0))
        | ~ r2_hidden(X1,a_2_0_waybel_3(sK0,X0))
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X1,a_2_0_waybel_3(sK0,X0)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(resolution,[],[f495,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f495,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK15(X0,sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK15(X0,sK0,X1),a_2_0_waybel_3(sK0,X1))
        | ~ r2_hidden(X0,a_2_0_waybel_3(sK0,X1)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(duplicate_literal_removal,[],[f494])).

fof(f494,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK15(X0,sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK15(X0,sK0,X1),a_2_0_waybel_3(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_0_waybel_3(sK0,X1)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(resolution,[],[f417,f416])).

fof(f416,plain,
    ( ! [X41,X40] :
        ( r1_waybel_3(sK0,sK15(X41,sK0,X40),X40)
        | ~ m1_subset_1(X40,u1_struct_0(sK0))
        | ~ r2_hidden(X41,a_2_0_waybel_3(sK0,X40)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(subsumption_resolution,[],[f353,f402])).

fof(f353,plain,
    ( ! [X41,X40] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X40,u1_struct_0(sK0))
        | r1_waybel_3(sK0,sK15(X41,sK0,X40),X40)
        | ~ r2_hidden(X41,a_2_0_waybel_3(sK0,X40)) )
    | ~ spl18_4
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f280,f211])).

fof(f280,plain,
    ( ! [X41,X40] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X40,u1_struct_0(sK0))
        | r1_waybel_3(sK0,sK15(X41,sK0,X40),X40)
        | ~ r2_hidden(X41,a_2_0_waybel_3(sK0,X40)) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f181])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_waybel_3(X1,sK15(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f417,plain,
    ( ! [X43,X42] :
        ( ~ r1_waybel_3(sK0,X43,X42)
        | ~ m1_subset_1(X43,u1_struct_0(sK0))
        | ~ m1_subset_1(X42,u1_struct_0(sK0))
        | r2_hidden(X43,a_2_0_waybel_3(sK0,X42)) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(subsumption_resolution,[],[f354,f402])).

fof(f354,plain,
    ( ! [X43,X42] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X42,u1_struct_0(sK0))
        | ~ m1_subset_1(X43,u1_struct_0(sK0))
        | ~ r1_waybel_3(sK0,X43,X42)
        | r2_hidden(X43,a_2_0_waybel_3(sK0,X42)) )
    | ~ spl18_4
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f281,f211])).

fof(f281,plain,
    ( ! [X43,X42] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X42,u1_struct_0(sK0))
        | ~ m1_subset_1(X43,u1_struct_0(sK0))
        | ~ r1_waybel_3(sK0,X43,X42)
        | r2_hidden(X43,a_2_0_waybel_3(sK0,X42)) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f190])).

fof(f190,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r1_waybel_3(X1,X3,X2)
      | r2_hidden(X3,a_2_0_waybel_3(X1,X2)) ) ),
    inference(equality_resolution,[],[f182])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ r1_waybel_3(X1,X3,X2)
      | r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f2086,plain,
    ( ~ m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ r2_hidden(sK12(sK0,sK7(sK0,sK1),sK2),sK2)
    | ~ v1_waybel_7(sK7(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | ~ spl18_77
    | ~ spl18_78
    | ~ spl18_178 ),
    inference(subsumption_resolution,[],[f1075,f2069])).

fof(f1075,plain,
    ( ~ m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ r2_hidden(sK12(sK0,sK7(sK0,sK1),sK2),sK2)
    | ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ v1_waybel_7(sK7(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | ~ spl18_77
    | ~ spl18_78 ),
    inference(subsumption_resolution,[],[f1074,f828])).

fof(f1074,plain,
    ( ~ m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ r2_hidden(sK12(sK0,sK7(sK0,sK1),sK2),sK2)
    | ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ v1_waybel_7(sK7(sK0,sK1),sK0)
    | v1_xboole_0(sK7(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | ~ spl18_78 ),
    inference(subsumption_resolution,[],[f1073,f834])).

fof(f1073,plain,
    ( ~ m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ r2_hidden(sK12(sK0,sK7(sK0,sK1),sK2),sK2)
    | ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK7(sK0,sK1),sK0)
    | v1_xboole_0(sK7(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | ~ spl18_78 ),
    inference(subsumption_resolution,[],[f1070,f822])).

fof(f1070,plain,
    ( ~ m1_subset_1(sK12(sK0,sK7(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ r2_hidden(sK12(sK0,sK7(sK0,sK1),sK2),sK2)
    | ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ v1_waybel_0(sK7(sK0,sK1),sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK7(sK0,sK1),sK0)
    | v1_xboole_0(sK7(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),sK7(sK0,sK1))
    | ~ spl18_1
    | ~ spl18_2
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_22
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | ~ spl18_78 ),
    inference(resolution,[],[f1067,f647])).

fof(f1067,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK7(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | ~ spl18_78 ),
    inference(duplicate_literal_removal,[],[f1064])).

fof(f1064,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK7(sK0,sK1))
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | ~ spl18_78 ),
    inference(resolution,[],[f906,f87])).

fof(f87,plain,(
    ! [X3] :
      ( ~ r3_orders_2(sK0,X3,sK1)
      | ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X2)
              & ~ v1_xboole_0(X2) )
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_waybel_3(X0,k2_yellow_0(X0,X2),X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X2)
              & ~ v1_xboole_0(X2) )
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v4_waybel_7(X1,X0)
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v1_finset_1(X2)
                    & ~ v1_xboole_0(X2) )
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,u1_struct_0(X0))
                         => ~ ( r3_orders_2(X0,X3,X1)
                              & r2_hidden(X3,X2) ) )
                      & r1_waybel_3(X0,k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_finset_1(X2)
                  & ~ v1_xboole_0(X2) )
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( r3_orders_2(X0,X3,X1)
                            & r2_hidden(X3,X2) ) )
                    & r1_waybel_3(X0,k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',t39_waybel_7)).

fof(f906,plain,
    ( ! [X1] :
        ( r3_orders_2(sK0,X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK7(sK0,sK1)) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | ~ spl18_78 ),
    inference(subsumption_resolution,[],[f904,f368])).

fof(f904,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK7(sK0,sK1))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_orders_2(sK0,X1,sK1) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | ~ spl18_78 ),
    inference(resolution,[],[f863,f413])).

fof(f413,plain,
    ( ! [X35,X34] :
        ( ~ r1_orders_2(sK0,X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(sK0))
        | ~ m1_subset_1(X34,u1_struct_0(sK0))
        | r3_orders_2(sK0,X34,X35) )
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(subsumption_resolution,[],[f350,f402])).

fof(f350,plain,
    ( ! [X35,X34] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X34,u1_struct_0(sK0))
        | ~ m1_subset_1(X35,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X34,X35)
        | r3_orders_2(sK0,X34,X35) )
    | ~ spl18_4
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f277,f211])).

fof(f277,plain,
    ( ! [X35,X34] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X34,u1_struct_0(sK0))
        | ~ m1_subset_1(X35,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X34,X35)
        | r3_orders_2(sK0,X34,X35) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',redefinition_r3_orders_2)).

fof(f863,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK1)
        | ~ r2_hidden(X0,sK7(sK0,sK1)) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | ~ spl18_78 ),
    inference(subsumption_resolution,[],[f849,f834])).

fof(f849,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK1)
        | ~ r2_hidden(X0,sK7(sK0,sK1))
        | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74 ),
    inference(subsumption_resolution,[],[f689,f822])).

fof(f689,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK1)
        | ~ v1_waybel_0(sK7(sK0,sK1),sK0)
        | ~ r2_hidden(X0,sK7(sK0,sK1))
        | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_32
    | ~ spl18_38 ),
    inference(superposition,[],[f654,f473])).

fof(f473,plain,
    ( k1_yellow_0(sK0,sK7(sK0,sK1)) = sK1
    | ~ spl18_38 ),
    inference(avatar_component_clause,[],[f472])).

fof(f654,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,k1_yellow_0(sK0,X0))
        | ~ v1_waybel_0(X0,sK0)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_32 ),
    inference(subsumption_resolution,[],[f653,f183])).

fof(f653,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | r1_orders_2(sK0,X1,k1_yellow_0(sK0,X0)) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_32 ),
    inference(subsumption_resolution,[],[f652,f175])).

fof(f652,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | r1_orders_2(sK0,X1,k1_yellow_0(sK0,X0)) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_32 ),
    inference(subsumption_resolution,[],[f650,f276])).

fof(f276,plain,
    ( ! [X33] : m1_subset_1(k1_yellow_0(sK0,X33),u1_struct_0(sK0))
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',dt_k1_yellow_0)).

fof(f650,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | r1_orders_2(sK0,X1,k1_yellow_0(sK0,X0))
        | ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_32 ),
    inference(resolution,[],[f464,f255])).

fof(f255,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(sK0,X2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',d9_lattice3)).

fof(f464,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,X0,k1_yellow_0(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK0) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_32 ),
    inference(resolution,[],[f442,f396])).

fof(f396,plain,
    ( ! [X3] :
        ( ~ r1_yellow_0(sK0,X3)
        | r2_lattice3(sK0,X3,k1_yellow_0(sK0,X3)) )
    | ~ spl18_8
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f395,f225])).

fof(f395,plain,
    ( ! [X3] :
        ( ~ v5_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X3)
        | r2_lattice3(sK0,X3,k1_yellow_0(sK0,X3)) )
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f386,f253])).

fof(f386,plain,
    ( ! [X3] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X3)
        | r2_lattice3(sK0,X3,k1_yellow_0(sK0,X3)) )
    | ~ spl18_16 ),
    inference(resolution,[],[f276,f187])).

fof(f187,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,k1_yellow_0(X0,X2)) ) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,X2) != X1
      | ~ r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',t30_yellow_0)).

fof(f442,plain,
    ( ! [X7] :
        ( r1_yellow_0(sK0,X7)
        | ~ v1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X7) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_32 ),
    inference(subsumption_resolution,[],[f411,f426])).

fof(f426,plain,
    ( v24_waybel_0(sK0)
    | ~ spl18_32 ),
    inference(avatar_component_clause,[],[f425])).

fof(f411,plain,
    ( ! [X7] :
        ( v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X7)
        | ~ v24_waybel_0(sK0) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16
    | ~ spl18_29 ),
    inference(subsumption_resolution,[],[f284,f402])).

fof(f284,plain,
    ( ! [X7] :
        ( v2_struct_0(sK0)
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X7)
        | ~ v24_waybel_0(sK0) )
    | ~ spl18_4
    | ~ spl18_8
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f283,f225])).

fof(f283,plain,
    ( ! [X7] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X7)
        | ~ v24_waybel_0(sK0) )
    | ~ spl18_4
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f258,f211])).

fof(f258,plain,
    ( ! [X7] :
        ( ~ v3_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X7)
        | ~ v1_waybel_0(X7,sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X7)
        | ~ v24_waybel_0(sK0) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_yellow_0(X0,X1)
      | ~ v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => r1_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',t75_waybel_0)).

fof(f2103,plain,
    ( ~ spl18_20
    | ~ spl18_26
    | spl18_181 ),
    inference(avatar_contradiction_clause,[],[f2102])).

fof(f2102,plain,
    ( $false
    | ~ spl18_20
    | ~ spl18_26
    | ~ spl18_181 ),
    inference(subsumption_resolution,[],[f2100,f368])).

fof(f2100,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl18_26
    | ~ spl18_181 ),
    inference(resolution,[],[f2078,f399])).

fof(f399,plain,
    ( ! [X44] :
        ( r3_orders_2(sK0,X44,X44)
        | ~ m1_subset_1(X44,u1_struct_0(sK0)) )
    | ~ spl18_26 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl18_26
  <=> ! [X44] :
        ( ~ m1_subset_1(X44,u1_struct_0(sK0))
        | r3_orders_2(sK0,X44,X44) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_26])])).

fof(f2078,plain,
    ( ~ r3_orders_2(sK0,sK1,sK1)
    | ~ spl18_181 ),
    inference(avatar_component_clause,[],[f2077])).

fof(f2077,plain,
    ( spl18_181
  <=> ~ r3_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_181])])).

fof(f2084,plain,
    ( ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | spl18_179 ),
    inference(avatar_contradiction_clause,[],[f2083])).

fof(f2083,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | ~ spl18_179 ),
    inference(subsumption_resolution,[],[f2082,f361])).

fof(f2082,plain,
    ( ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_179 ),
    inference(subsumption_resolution,[],[f2081,f368])).

fof(f2081,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_179 ),
    inference(resolution,[],[f2072,f299])).

fof(f2072,plain,
    ( ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ spl18_179 ),
    inference(avatar_component_clause,[],[f2071])).

fof(f2071,plain,
    ( spl18_179
  <=> ~ v12_waybel_0(sK7(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_179])])).

fof(f2079,plain,
    ( ~ spl18_179
    | ~ spl18_181
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | spl18_77
    | ~ spl18_78
    | spl18_173 ),
    inference(avatar_split_clause,[],[f2023,f2012,f833,f827,f821,f472,f425,f367,f252,f245,f238,f224,f217,f210,f2077,f2071])).

fof(f245,plain,
    ( spl18_14
  <=> v3_waybel_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_14])])).

fof(f2012,plain,
    ( spl18_173
  <=> ~ r1_tarski(k1_waybel_3(sK0,sK1),sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_173])])).

fof(f2023,plain,
    ( ~ r3_orders_2(sK0,sK1,sK1)
    | ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_32
    | ~ spl18_38
    | ~ spl18_74
    | ~ spl18_77
    | ~ spl18_78
    | ~ spl18_173 ),
    inference(forward_demodulation,[],[f2022,f473])).

fof(f2022,plain,
    ( ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ r3_orders_2(sK0,sK1,k1_yellow_0(sK0,sK7(sK0,sK1)))
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_32
    | ~ spl18_74
    | ~ spl18_77
    | ~ spl18_78
    | ~ spl18_173 ),
    inference(subsumption_resolution,[],[f2021,f368])).

fof(f2021,plain,
    ( ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ r3_orders_2(sK0,sK1,k1_yellow_0(sK0,sK7(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_32
    | ~ spl18_74
    | ~ spl18_77
    | ~ spl18_78
    | ~ spl18_173 ),
    inference(subsumption_resolution,[],[f2020,f834])).

fof(f2020,plain,
    ( ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r3_orders_2(sK0,sK1,k1_yellow_0(sK0,sK7(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_32
    | ~ spl18_74
    | ~ spl18_77
    | ~ spl18_173 ),
    inference(subsumption_resolution,[],[f2019,f822])).

fof(f2019,plain,
    ( ~ v1_waybel_0(sK7(sK0,sK1),sK0)
    | ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r3_orders_2(sK0,sK1,k1_yellow_0(sK0,sK7(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_32
    | ~ spl18_77
    | ~ spl18_173 ),
    inference(subsumption_resolution,[],[f2017,f828])).

fof(f2017,plain,
    ( v1_xboole_0(sK7(sK0,sK1))
    | ~ v1_waybel_0(sK7(sK0,sK1),sK0)
    | ~ v12_waybel_0(sK7(sK0,sK1),sK0)
    | ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r3_orders_2(sK0,sK1,k1_yellow_0(sK0,sK7(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_32
    | ~ spl18_173 ),
    inference(resolution,[],[f2013,f445])).

fof(f445,plain,
    ( ! [X21,X22] :
        ( r1_tarski(k1_waybel_3(sK0,X21),X22)
        | v1_xboole_0(X22)
        | ~ v1_waybel_0(X22,sK0)
        | ~ v12_waybel_0(X22,sK0)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r3_orders_2(sK0,X21,k1_yellow_0(sK0,X22))
        | ~ m1_subset_1(X21,u1_struct_0(sK0)) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_32 ),
    inference(subsumption_resolution,[],[f314,f426])).

fof(f314,plain,
    ( ! [X21,X22] :
        ( ~ v24_waybel_0(sK0)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | v1_xboole_0(X22)
        | ~ v1_waybel_0(X22,sK0)
        | ~ v12_waybel_0(X22,sK0)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r3_orders_2(sK0,X21,k1_yellow_0(sK0,X22))
        | r1_tarski(k1_waybel_3(sK0,X21),X22) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_14
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f313,f246])).

fof(f246,plain,
    ( v3_waybel_3(sK0)
    | ~ spl18_14 ),
    inference(avatar_component_clause,[],[f245])).

fof(f313,plain,
    ( ! [X21,X22] :
        ( ~ v24_waybel_0(sK0)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | v1_xboole_0(X22)
        | ~ v1_waybel_0(X22,sK0)
        | ~ v12_waybel_0(X22,sK0)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r3_orders_2(sK0,X21,k1_yellow_0(sK0,X22))
        | r1_tarski(k1_waybel_3(sK0,X21),X22)
        | ~ v3_waybel_3(sK0) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f312,f211])).

fof(f312,plain,
    ( ! [X21,X22] :
        ( ~ v24_waybel_0(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | v1_xboole_0(X22)
        | ~ v1_waybel_0(X22,sK0)
        | ~ v12_waybel_0(X22,sK0)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r3_orders_2(sK0,X21,k1_yellow_0(sK0,X22))
        | r1_tarski(k1_waybel_3(sK0,X21),X22)
        | ~ v3_waybel_3(sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f311,f239])).

fof(f311,plain,
    ( ! [X21,X22] :
        ( ~ v2_lattice3(sK0)
        | ~ v24_waybel_0(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | v1_xboole_0(X22)
        | ~ v1_waybel_0(X22,sK0)
        | ~ v12_waybel_0(X22,sK0)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r3_orders_2(sK0,X21,k1_yellow_0(sK0,X22))
        | r1_tarski(k1_waybel_3(sK0,X21),X22)
        | ~ v3_waybel_3(sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f310,f225])).

fof(f310,plain,
    ( ! [X21,X22] :
        ( ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v24_waybel_0(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | v1_xboole_0(X22)
        | ~ v1_waybel_0(X22,sK0)
        | ~ v12_waybel_0(X22,sK0)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r3_orders_2(sK0,X21,k1_yellow_0(sK0,X22))
        | r1_tarski(k1_waybel_3(sK0,X21),X22)
        | ~ v3_waybel_3(sK0) )
    | ~ spl18_6
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f268,f218])).

fof(f268,plain,
    ( ! [X21,X22] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v24_waybel_0(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | v1_xboole_0(X22)
        | ~ v1_waybel_0(X22,sK0)
        | ~ v12_waybel_0(X22,sK0)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r3_orders_2(sK0,X21,k1_yellow_0(sK0,X22))
        | r1_tarski(k1_waybel_3(sK0,X21),X22)
        | ~ v3_waybel_3(sK0) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v24_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(X2)
      | ~ v1_waybel_0(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r3_orders_2(X0,X1,k1_yellow_0(X0,X2))
      | r1_tarski(k1_waybel_3(X0,X1),X2)
      | ~ v3_waybel_3(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( v3_waybel_3(X0)
      <=> ! [X1] :
            ( ( ! [X2] :
                  ( r1_tarski(k1_waybel_3(X0,X1),X2)
                  | ~ r3_orders_2(X0,X1,k1_yellow_0(X0,X2))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) )
              & r3_orders_2(X0,X1,k1_yellow_0(X0,k1_waybel_3(X0,X1)))
              & m1_subset_1(k1_waybel_3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(k1_waybel_3(X0,X1),X0)
              & v1_waybel_0(k1_waybel_3(X0,X1),X0)
              & ~ v1_xboole_0(k1_waybel_3(X0,X1)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( v3_waybel_3(X0)
      <=> ! [X1] :
            ( ( ! [X2] :
                  ( r1_tarski(k1_waybel_3(X0,X1),X2)
                  | ~ r3_orders_2(X0,X1,k1_yellow_0(X0,X2))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) )
              & r3_orders_2(X0,X1,k1_yellow_0(X0,k1_waybel_3(X0,X1)))
              & m1_subset_1(k1_waybel_3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(k1_waybel_3(X0,X1),X0)
              & v1_waybel_0(k1_waybel_3(X0,X1),X0)
              & ~ v1_xboole_0(k1_waybel_3(X0,X1)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v24_waybel_0(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v24_waybel_0(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_waybel_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v12_waybel_0(X2,X0)
                    & v1_waybel_0(X2,X0)
                    & ~ v1_xboole_0(X2) )
                 => ( r3_orders_2(X0,X1,k1_yellow_0(X0,X2))
                   => r1_tarski(k1_waybel_3(X0,X1),X2) ) )
              & r3_orders_2(X0,X1,k1_yellow_0(X0,k1_waybel_3(X0,X1)))
              & m1_subset_1(k1_waybel_3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(k1_waybel_3(X0,X1),X0)
              & v1_waybel_0(k1_waybel_3(X0,X1),X0)
              & ~ v1_xboole_0(k1_waybel_3(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',t1_waybel_5)).

fof(f2013,plain,
    ( ~ r1_tarski(k1_waybel_3(sK0,sK1),sK7(sK0,sK1))
    | ~ spl18_173 ),
    inference(avatar_component_clause,[],[f2012])).

fof(f2014,plain,
    ( ~ spl18_173
    | spl18_167 ),
    inference(avatar_split_clause,[],[f1994,f1987,f2012])).

fof(f1987,plain,
    ( spl18_167
  <=> ~ m1_subset_1(k1_waybel_3(sK0,sK1),k1_zfmisc_1(sK7(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_167])])).

fof(f1994,plain,
    ( ~ r1_tarski(k1_waybel_3(sK0,sK1),sK7(sK0,sK1))
    | ~ spl18_167 ),
    inference(resolution,[],[f1988,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',t3_subset)).

fof(f1988,plain,
    ( ~ m1_subset_1(k1_waybel_3(sK0,sK1),k1_zfmisc_1(sK7(sK0,sK1)))
    | ~ spl18_167 ),
    inference(avatar_component_clause,[],[f1987])).

fof(f878,plain,
    ( ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | ~ spl18_76 ),
    inference(avatar_contradiction_clause,[],[f877])).

fof(f877,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | ~ spl18_76 ),
    inference(subsumption_resolution,[],[f876,f361])).

fof(f876,plain,
    ( ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_76 ),
    inference(subsumption_resolution,[],[f875,f211])).

fof(f875,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_76 ),
    inference(subsumption_resolution,[],[f874,f368])).

fof(f874,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_76 ),
    inference(subsumption_resolution,[],[f873,f253])).

fof(f873,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_76 ),
    inference(subsumption_resolution,[],[f872,f239])).

fof(f872,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_76 ),
    inference(subsumption_resolution,[],[f871,f232])).

fof(f871,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_76 ),
    inference(subsumption_resolution,[],[f870,f225])).

fof(f870,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_76 ),
    inference(subsumption_resolution,[],[f865,f218])).

fof(f865,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_76 ),
    inference(resolution,[],[f831,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK7(X0,X1))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f831,plain,
    ( v1_xboole_0(sK7(sK0,sK1))
    | ~ spl18_76 ),
    inference(avatar_component_clause,[],[f830])).

fof(f830,plain,
    ( spl18_76
  <=> v1_xboole_0(sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_76])])).

fof(f861,plain,
    ( ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | spl18_79 ),
    inference(avatar_contradiction_clause,[],[f860])).

fof(f860,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | ~ spl18_79 ),
    inference(subsumption_resolution,[],[f859,f361])).

fof(f859,plain,
    ( ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_79 ),
    inference(subsumption_resolution,[],[f858,f211])).

fof(f858,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_79 ),
    inference(subsumption_resolution,[],[f857,f368])).

fof(f857,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_79 ),
    inference(subsumption_resolution,[],[f856,f253])).

fof(f856,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_79 ),
    inference(subsumption_resolution,[],[f855,f239])).

fof(f855,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_79 ),
    inference(subsumption_resolution,[],[f854,f232])).

fof(f854,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_79 ),
    inference(subsumption_resolution,[],[f853,f225])).

fof(f853,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_6
    | ~ spl18_79 ),
    inference(subsumption_resolution,[],[f851,f218])).

fof(f851,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_79 ),
    inference(resolution,[],[f837,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f837,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl18_79 ),
    inference(avatar_component_clause,[],[f836])).

fof(f836,plain,
    ( spl18_79
  <=> ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_79])])).

fof(f848,plain,
    ( ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | spl18_75 ),
    inference(avatar_contradiction_clause,[],[f847])).

fof(f847,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20
    | ~ spl18_75 ),
    inference(subsumption_resolution,[],[f846,f361])).

fof(f846,plain,
    ( ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_75 ),
    inference(subsumption_resolution,[],[f845,f368])).

fof(f845,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v4_waybel_7(sK1,sK0)
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_75 ),
    inference(resolution,[],[f825,f294])).

fof(f825,plain,
    ( ~ v1_waybel_0(sK7(sK0,sK1),sK0)
    | ~ spl18_75 ),
    inference(avatar_component_clause,[],[f824])).

fof(f824,plain,
    ( spl18_75
  <=> ~ v1_waybel_0(sK7(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_75])])).

fof(f555,plain,
    ( spl18_48
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_20
    | spl18_29
    | ~ spl18_40 ),
    inference(avatar_split_clause,[],[f528,f503,f401,f367,f252,f210,f553])).

fof(f528,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK2),k1_waybel_3(sK0,sK1))
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_29
    | ~ spl18_40 ),
    inference(subsumption_resolution,[],[f527,f368])).

fof(f527,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK2),k1_waybel_3(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_40 ),
    inference(superposition,[],[f504,f412])).

fof(f520,plain,
    ( ~ spl18_16
    | spl18_43 ),
    inference(avatar_contradiction_clause,[],[f519])).

fof(f519,plain,
    ( $false
    | ~ spl18_16
    | ~ spl18_43 ),
    inference(subsumption_resolution,[],[f517,f253])).

fof(f517,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl18_43 ),
    inference(resolution,[],[f510,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',dt_k2_yellow_0)).

fof(f510,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ spl18_43 ),
    inference(avatar_component_clause,[],[f509])).

fof(f509,plain,
    ( spl18_43
  <=> ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_43])])).

fof(f511,plain,
    ( spl18_40
    | ~ spl18_43
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_24
    | spl18_29 ),
    inference(avatar_split_clause,[],[f496,f401,f381,f367,f252,f210,f509,f503])).

fof(f381,plain,
    ( spl18_24
  <=> r1_waybel_3(sK0,k2_yellow_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_24])])).

fof(f496,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | r2_hidden(k2_yellow_0(sK0,sK2),a_2_0_waybel_3(sK0,sK1))
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_20
    | ~ spl18_24
    | ~ spl18_29 ),
    inference(subsumption_resolution,[],[f493,f368])).

fof(f493,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k2_yellow_0(sK0,sK2),a_2_0_waybel_3(sK0,sK1))
    | ~ spl18_4
    | ~ spl18_16
    | ~ spl18_24
    | ~ spl18_29 ),
    inference(resolution,[],[f417,f382])).

fof(f382,plain,
    ( r1_waybel_3(sK0,k2_yellow_0(sK0,sK2),sK1)
    | ~ spl18_24 ),
    inference(avatar_component_clause,[],[f381])).

fof(f474,plain,
    ( spl18_38
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20 ),
    inference(avatar_split_clause,[],[f467,f367,f360,f252,f238,f231,f224,f217,f210,f472])).

fof(f467,plain,
    ( k1_yellow_0(sK0,sK7(sK0,sK1)) = sK1
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f466,f368])).

fof(f466,plain,
    ( k1_yellow_0(sK0,sK7(sK0,sK1)) = sK1
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_18 ),
    inference(resolution,[],[f309,f361])).

fof(f309,plain,
    ( ! [X20] :
        ( ~ v4_waybel_7(X20,sK0)
        | k1_yellow_0(sK0,sK7(sK0,X20)) = X20
        | ~ m1_subset_1(X20,u1_struct_0(sK0)) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f308,f211])).

fof(f308,plain,
    ( ! [X20] :
        ( ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X20,u1_struct_0(sK0))
        | k1_yellow_0(sK0,sK7(sK0,X20)) = X20
        | ~ v4_waybel_7(X20,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_12
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f307,f239])).

fof(f307,plain,
    ( ! [X20] :
        ( ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X20,u1_struct_0(sK0))
        | k1_yellow_0(sK0,sK7(sK0,X20)) = X20
        | ~ v4_waybel_7(X20,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_10
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f306,f232])).

fof(f306,plain,
    ( ! [X20] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X20,u1_struct_0(sK0))
        | k1_yellow_0(sK0,sK7(sK0,X20)) = X20
        | ~ v4_waybel_7(X20,sK0) )
    | ~ spl18_6
    | ~ spl18_8
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f305,f225])).

fof(f305,plain,
    ( ! [X20] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X20,u1_struct_0(sK0))
        | k1_yellow_0(sK0,sK7(sK0,X20)) = X20
        | ~ v4_waybel_7(X20,sK0) )
    | ~ spl18_6
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f267,f218])).

fof(f267,plain,
    ( ! [X20] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X20,u1_struct_0(sK0))
        | k1_yellow_0(sK0,sK7(sK0,X20)) = X20
        | ~ v4_waybel_7(X20,sK0) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,sK7(X0,X1)) = X1
      | ~ v4_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f441,plain,
    ( ~ spl18_4
    | ~ spl18_14
    | ~ spl18_16
    | spl18_29
    | spl18_33 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_14
    | ~ spl18_16
    | ~ spl18_29
    | ~ spl18_33 ),
    inference(subsumption_resolution,[],[f439,f253])).

fof(f439,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl18_4
    | ~ spl18_14
    | ~ spl18_29
    | ~ spl18_33 ),
    inference(subsumption_resolution,[],[f438,f246])).

fof(f438,plain,
    ( ~ v3_waybel_3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl18_4
    | ~ spl18_29
    | ~ spl18_33 ),
    inference(subsumption_resolution,[],[f437,f211])).

fof(f437,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl18_29
    | ~ spl18_33 ),
    inference(subsumption_resolution,[],[f432,f402])).

fof(f432,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl18_33 ),
    inference(resolution,[],[f429,f104])).

fof(f104,plain,(
    ! [X0] :
      ( v24_waybel_0(X0)
      | v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v2_waybel_3(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v2_waybel_3(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_waybel_3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_3(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',cc4_waybel_3)).

fof(f429,plain,
    ( ~ v24_waybel_0(sK0)
    | ~ spl18_33 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl18_33
  <=> ~ v24_waybel_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_33])])).

fof(f410,plain,
    ( ~ spl18_12
    | ~ spl18_16
    | ~ spl18_28 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl18_12
    | ~ spl18_16
    | ~ spl18_28 ),
    inference(subsumption_resolution,[],[f408,f253])).

fof(f408,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl18_12
    | ~ spl18_28 ),
    inference(subsumption_resolution,[],[f407,f239])).

fof(f407,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl18_28 ),
    inference(resolution,[],[f405,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',cc2_lattice3)).

fof(f405,plain,
    ( v2_struct_0(sK0)
    | ~ spl18_28 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl18_28
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_28])])).

fof(f406,plain,
    ( spl18_26
    | spl18_28
    | ~ spl18_4
    | ~ spl18_16 ),
    inference(avatar_split_clause,[],[f355,f252,f210,f404,f398])).

fof(f355,plain,
    ( ! [X44] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X44,u1_struct_0(sK0))
        | r3_orders_2(sK0,X44,X44) )
    | ~ spl18_4
    | ~ spl18_16 ),
    inference(subsumption_resolution,[],[f282,f211])).

fof(f282,plain,
    ( ! [X44] :
        ( v2_struct_0(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X44,u1_struct_0(sK0))
        | r3_orders_2(sK0,X44,X44) )
    | ~ spl18_16 ),
    inference(resolution,[],[f253,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r3_orders_2(X1,X0,X0) ) ),
    inference(condensation,[],[f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t39_waybel_7.p',reflexivity_r3_orders_2)).

fof(f383,plain,(
    spl18_24 ),
    inference(avatar_split_clause,[],[f91,f381])).

fof(f91,plain,(
    r1_waybel_3(sK0,k2_yellow_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f376,plain,(
    spl18_22 ),
    inference(avatar_split_clause,[],[f90,f374])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f369,plain,(
    spl18_20 ),
    inference(avatar_split_clause,[],[f92,f367])).

fof(f92,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f362,plain,(
    spl18_18 ),
    inference(avatar_split_clause,[],[f93,f360])).

fof(f93,plain,(
    v4_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f254,plain,(
    spl18_16 ),
    inference(avatar_split_clause,[],[f100,f252])).

fof(f100,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f247,plain,(
    spl18_14 ),
    inference(avatar_split_clause,[],[f99,f245])).

fof(f99,plain,(
    v3_waybel_3(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f240,plain,(
    spl18_12 ),
    inference(avatar_split_clause,[],[f98,f238])).

fof(f98,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f233,plain,(
    spl18_10 ),
    inference(avatar_split_clause,[],[f97,f231])).

fof(f97,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f226,plain,(
    spl18_8 ),
    inference(avatar_split_clause,[],[f96,f224])).

fof(f96,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f219,plain,(
    spl18_6 ),
    inference(avatar_split_clause,[],[f95,f217])).

fof(f95,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f212,plain,(
    spl18_4 ),
    inference(avatar_split_clause,[],[f94,f210])).

fof(f94,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f205,plain,(
    spl18_2 ),
    inference(avatar_split_clause,[],[f89,f203])).

fof(f89,plain,(
    v1_finset_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f198,plain,(
    ~ spl18_1 ),
    inference(avatar_split_clause,[],[f88,f196])).

fof(f88,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
