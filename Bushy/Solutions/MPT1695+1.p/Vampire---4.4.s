%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t75_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:01 EDT 2019

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  538 (1584 expanded)
%              Number of leaves         :   95 ( 692 expanded)
%              Depth                    :   19
%              Number of atoms          : 3321 (10860 expanded)
%              Number of equality atoms :   60 ( 328 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f157,f164,f171,f178,f205,f218,f234,f268,f277,f285,f310,f449,f481,f529,f562,f608,f619,f729,f737,f797,f804,f831,f857,f1092,f1196,f1442,f1478,f1555,f2138,f2168,f3919,f3932,f3985,f3997,f4261,f4271,f4287,f4353,f4392,f4501,f4598,f5011,f5030,f5140,f5194,f5216,f5248,f5369,f5469,f5512,f5532,f5562,f5609,f5650,f5653,f5763,f5784,f5788,f5798,f5825,f5861,f5874,f5902,f5933,f6021,f6324,f6357,f6365,f6383])).

fof(f6383,plain,
    ( spl15_17
    | ~ spl15_852 ),
    inference(avatar_contradiction_clause,[],[f6382])).

fof(f6382,plain,
    ( $false
    | ~ spl15_17
    | ~ spl15_852 ),
    inference(subsumption_resolution,[],[f6376,f204])).

fof(f204,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl15_17 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl15_17
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_17])])).

fof(f6376,plain,
    ( v1_xboole_0(sK1)
    | ~ spl15_852 ),
    inference(resolution,[],[f6364,f225])).

fof(f225,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f128,f125])).

fof(f125,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f15,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',existence_m1_subset_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',t2_subset)).

fof(f6364,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl15_852 ),
    inference(avatar_component_clause,[],[f6363])).

fof(f6363,plain,
    ( spl15_852
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_852])])).

fof(f6365,plain,
    ( spl15_852
    | ~ spl15_850 ),
    inference(avatar_split_clause,[],[f6360,f6355,f6363])).

fof(f6355,plain,
    ( spl15_850
  <=> sP14(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_850])])).

fof(f6360,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl15_850 ),
    inference(resolution,[],[f6356,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ sP14(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f137,f142_D])).

fof(f142,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP14(X1) ) ),
    inference(cnf_transformation,[],[f142_D])).

fof(f142_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP14(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP14])])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',t5_subset)).

fof(f6356,plain,
    ( sP14(sK1)
    | ~ spl15_850 ),
    inference(avatar_component_clause,[],[f6355])).

fof(f6357,plain,
    ( spl15_850
    | ~ spl15_22
    | ~ spl15_132 ),
    inference(avatar_split_clause,[],[f6335,f834,f232,f6355])).

fof(f232,plain,
    ( spl15_22
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | sP14(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).

fof(f834,plain,
    ( spl15_132
  <=> m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_132])])).

fof(f6335,plain,
    ( sP14(sK1)
    | ~ spl15_22
    | ~ spl15_132 ),
    inference(resolution,[],[f835,f233])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | sP14(X0) )
    | ~ spl15_22 ),
    inference(avatar_component_clause,[],[f232])).

fof(f835,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl15_132 ),
    inference(avatar_component_clause,[],[f834])).

fof(f6324,plain,
    ( spl15_132
    | ~ spl15_40
    | ~ spl15_130 ),
    inference(avatar_split_clause,[],[f6131,f829,f308,f834])).

fof(f308,plain,
    ( spl15_40
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_40])])).

fof(f829,plain,
    ( spl15_130
  <=> u1_struct_0(sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_130])])).

fof(f6131,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl15_40
    | ~ spl15_130 ),
    inference(backward_demodulation,[],[f830,f309])).

fof(f309,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_40 ),
    inference(avatar_component_clause,[],[f308])).

fof(f830,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl15_130 ),
    inference(avatar_component_clause,[],[f829])).

fof(f6021,plain,
    ( ~ spl15_6
    | spl15_35
    | ~ spl15_728
    | spl15_783
    | ~ spl15_792
    | ~ spl15_824 ),
    inference(avatar_contradiction_clause,[],[f6020])).

fof(f6020,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_35
    | ~ spl15_728
    | ~ spl15_783
    | ~ spl15_792
    | ~ spl15_824 ),
    inference(subsumption_resolution,[],[f6019,f170])).

fof(f170,plain,
    ( l1_orders_2(sK0)
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl15_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f6019,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl15_35
    | ~ spl15_728
    | ~ spl15_783
    | ~ spl15_792
    | ~ spl15_824 ),
    inference(subsumption_resolution,[],[f6018,f5007])).

fof(f5007,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl15_728 ),
    inference(avatar_component_clause,[],[f5006])).

fof(f5006,plain,
    ( spl15_728
  <=> m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_728])])).

fof(f6018,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_35
    | ~ spl15_783
    | ~ spl15_792
    | ~ spl15_824 ),
    inference(subsumption_resolution,[],[f6017,f5522])).

fof(f5522,plain,
    ( r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ spl15_792 ),
    inference(avatar_component_clause,[],[f5521])).

fof(f5521,plain,
    ( spl15_792
  <=> r2_lattice3(sK0,sK1,sK9(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_792])])).

fof(f6017,plain,
    ( ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_35
    | ~ spl15_783
    | ~ spl15_824 ),
    inference(subsumption_resolution,[],[f6016,f5435])).

fof(f5435,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl15_783 ),
    inference(avatar_component_clause,[],[f5434])).

fof(f5434,plain,
    ( spl15_783
  <=> ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_783])])).

fof(f6016,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_35
    | ~ spl15_824 ),
    inference(subsumption_resolution,[],[f6008,f284])).

fof(f284,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ spl15_35 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl15_35
  <=> ~ r1_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_35])])).

fof(f6008,plain,
    ( r1_yellow_0(sK0,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_824 ),
    inference(trivial_inequality_removal,[],[f6007])).

fof(f6007,plain,
    ( sK9(sK0,sK1) != sK9(sK0,sK1)
    | r1_yellow_0(sK0,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_824 ),
    inference(superposition,[],[f109,f5783])).

fof(f5783,plain,
    ( sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1)
    | ~ spl15_824 ),
    inference(avatar_component_clause,[],[f5782])).

fof(f5782,plain,
    ( spl15_824
  <=> sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_824])])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( sK2(X0,X1,X2) != X2
                  & ! [X4] :
                      ( r1_orders_2(X0,sK2(X0,X1,X2),X4)
                      | ~ r2_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X1,sK2(X0,X1,X2))
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X7] :
                  ( sK4(X0,X1) = X7
                  | ( ~ r1_orders_2(X0,X7,sK5(X0,X1,X7))
                    & r2_lattice3(X0,X1,sK5(X0,X1,X7))
                    & m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X7)
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X9] :
                  ( r1_orders_2(X0,sK4(X0,X1),X9)
                  | ~ r2_lattice3(X0,X1,X9)
                  | ~ m1_subset_1(X9,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK4(X0,X1))
              & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f60,f64,f63,f62,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X2 != X3
          & ! [X4] :
              ( r1_orders_2(X0,X3,X4)
              | ~ r2_lattice3(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK2(X0,X1,X2) != X2
        & ! [X4] :
            ( r1_orders_2(X0,sK2(X0,X1,X2),X4)
            | ~ r2_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X2,X5)
          & r2_lattice3(X0,X1,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X6] :
          ( ! [X7] :
              ( X6 = X7
              | ? [X8] :
                  ( ~ r1_orders_2(X0,X7,X8)
                  & r2_lattice3(X0,X1,X8)
                  & m1_subset_1(X8,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & ! [X9] :
              ( r1_orders_2(X0,X6,X9)
              | ~ r2_lattice3(X0,X1,X9)
              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( ! [X7] :
            ( sK4(X0,X1) = X7
            | ? [X8] :
                ( ~ r1_orders_2(X0,X7,X8)
                & r2_lattice3(X0,X1,X8)
                & m1_subset_1(X8,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X7)
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & ! [X9] :
            ( r1_orders_2(X0,sK4(X0,X1),X9)
            | ~ r2_lattice3(X0,X1,X9)
            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X7,X1,X0] :
      ( ? [X8] :
          ( ~ r1_orders_2(X0,X7,X8)
          & r2_lattice3(X0,X1,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X7,sK5(X0,X1,X7))
        & r2_lattice3(X0,X1,sK5(X0,X1,X7))
        & m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r2_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X2,X5)
                    & r2_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X6] :
                ( ! [X7] :
                    ( X6 = X7
                    | ? [X8] :
                        ( ~ r1_orders_2(X0,X7,X8)
                        & r2_lattice3(X0,X1,X8)
                        & m1_subset_1(X8,u1_struct_0(X0)) )
                    | ~ r2_lattice3(X0,X1,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                & ! [X9] :
                    ( r1_orders_2(X0,X6,X9)
                    | ~ r2_lattice3(X0,X1,X9)
                    | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X6)
                & m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r2_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X2,X5)
                    & r2_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( X2 = X3
                    | ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r2_lattice3(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & ! [X5] :
                    ( r1_orders_2(X0,X2,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',d7_yellow_0)).

fof(f5933,plain,
    ( ~ spl15_6
    | spl15_35
    | ~ spl15_728
    | spl15_783
    | spl15_789
    | ~ spl15_792 ),
    inference(avatar_contradiction_clause,[],[f5932])).

fof(f5932,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_35
    | ~ spl15_728
    | ~ spl15_783
    | ~ spl15_789
    | ~ spl15_792 ),
    inference(subsumption_resolution,[],[f5931,f170])).

fof(f5931,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl15_35
    | ~ spl15_728
    | ~ spl15_783
    | ~ spl15_789
    | ~ spl15_792 ),
    inference(subsumption_resolution,[],[f5930,f5007])).

fof(f5930,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_35
    | ~ spl15_783
    | ~ spl15_789
    | ~ spl15_792 ),
    inference(subsumption_resolution,[],[f5929,f5522])).

fof(f5929,plain,
    ( ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_35
    | ~ spl15_783
    | ~ spl15_789 ),
    inference(subsumption_resolution,[],[f5928,f5435])).

fof(f5928,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_35
    | ~ spl15_789 ),
    inference(subsumption_resolution,[],[f5926,f284])).

fof(f5926,plain,
    ( r1_yellow_0(sK0,sK1)
    | m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_789 ),
    inference(resolution,[],[f5502,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5502,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_789 ),
    inference(avatar_component_clause,[],[f5501])).

fof(f5501,plain,
    ( spl15_789
  <=> ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_789])])).

fof(f5902,plain,
    ( ~ spl15_6
    | spl15_35
    | ~ spl15_728
    | spl15_791
    | ~ spl15_792
    | ~ spl15_824 ),
    inference(avatar_contradiction_clause,[],[f5899])).

fof(f5899,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_35
    | ~ spl15_728
    | ~ spl15_791
    | ~ spl15_792
    | ~ spl15_824 ),
    inference(unit_resulting_resolution,[],[f170,f284,f5007,f5522,f5783,f5511,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5511,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_791 ),
    inference(avatar_component_clause,[],[f5510])).

fof(f5510,plain,
    ( spl15_791
  <=> ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_791])])).

fof(f5874,plain,
    ( ~ spl15_6
    | spl15_35
    | ~ spl15_728
    | ~ spl15_792
    | ~ spl15_824
    | ~ spl15_832 ),
    inference(avatar_contradiction_clause,[],[f5866])).

fof(f5866,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_35
    | ~ spl15_728
    | ~ spl15_792
    | ~ spl15_824
    | ~ spl15_832 ),
    inference(unit_resulting_resolution,[],[f170,f284,f5007,f5522,f5783,f5860,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5860,plain,
    ( r1_orders_2(sK0,sK9(sK0,sK1),sK3(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_832 ),
    inference(avatar_component_clause,[],[f5859])).

fof(f5859,plain,
    ( spl15_832
  <=> r1_orders_2(sK0,sK9(sK0,sK1),sK3(sK0,sK1,sK9(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_832])])).

fof(f5861,plain,
    ( spl15_832
    | ~ spl15_782
    | ~ spl15_790
    | ~ spl15_826 ),
    inference(avatar_split_clause,[],[f5836,f5786,f5507,f5437,f5859])).

fof(f5437,plain,
    ( spl15_782
  <=> m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_782])])).

fof(f5507,plain,
    ( spl15_790
  <=> r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_790])])).

fof(f5786,plain,
    ( spl15_826
  <=> ! [X0] :
        ( r1_orders_2(sK0,sK9(sK0,sK1),X0)
        | ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_826])])).

fof(f5836,plain,
    ( r1_orders_2(sK0,sK9(sK0,sK1),sK3(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_782
    | ~ spl15_790
    | ~ spl15_826 ),
    inference(subsumption_resolution,[],[f5830,f5438])).

fof(f5438,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl15_782 ),
    inference(avatar_component_clause,[],[f5437])).

fof(f5830,plain,
    ( r1_orders_2(sK0,sK9(sK0,sK1),sK3(sK0,sK1,sK9(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl15_790
    | ~ spl15_826 ),
    inference(resolution,[],[f5787,f5508])).

fof(f5508,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_790 ),
    inference(avatar_component_clause,[],[f5507])).

fof(f5787,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | r1_orders_2(sK0,sK9(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_826 ),
    inference(avatar_component_clause,[],[f5786])).

fof(f5825,plain,
    ( spl15_780
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | spl15_17
    | ~ spl15_32
    | spl15_35
    | ~ spl15_40
    | ~ spl15_750
    | ~ spl15_790 ),
    inference(avatar_split_clause,[],[f5823,f5507,f5192,f308,f283,f275,f203,f194,f169,f155,f148,f5431])).

fof(f5431,plain,
    ( spl15_780
  <=> ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_780])])).

fof(f148,plain,
    ( spl15_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f155,plain,
    ( spl15_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f194,plain,
    ( spl15_14
  <=> v24_waybel_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f275,plain,
    ( spl15_32
  <=> v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_32])])).

fof(f5192,plain,
    ( spl15_750
  <=> ! [X1,X0] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X0,sK9(sK0,sK1)))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK9(sK0,sK1))
        | r1_orders_2(sK0,sK2(sK0,X0,sK9(sK0,sK1)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_750])])).

fof(f5823,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_750
    | ~ spl15_790 ),
    inference(subsumption_resolution,[],[f5204,f5508])).

fof(f5204,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_750 ),
    inference(subsumption_resolution,[],[f5203,f149])).

fof(f149,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f148])).

fof(f5203,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_750 ),
    inference(subsumption_resolution,[],[f5202,f156])).

fof(f156,plain,
    ( v3_orders_2(sK0)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f155])).

fof(f5202,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_750 ),
    inference(subsumption_resolution,[],[f5201,f170])).

fof(f5201,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_750 ),
    inference(subsumption_resolution,[],[f5200,f195])).

fof(f195,plain,
    ( v24_waybel_0(sK0)
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f194])).

fof(f5200,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | ~ v24_waybel_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_750 ),
    inference(subsumption_resolution,[],[f5199,f204])).

fof(f5199,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | v1_xboole_0(sK1)
        | ~ v24_waybel_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_750 ),
    inference(subsumption_resolution,[],[f5198,f276])).

fof(f276,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl15_32 ),
    inference(avatar_component_clause,[],[f275])).

fof(f5198,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | ~ v1_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ v24_waybel_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_750 ),
    inference(subsumption_resolution,[],[f5197,f309])).

fof(f5197,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ v24_waybel_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_35
    | ~ spl15_750 ),
    inference(subsumption_resolution,[],[f5196,f284])).

fof(f5196,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_yellow_0(sK0,sK1)
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ v24_waybel_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_750 ),
    inference(resolution,[],[f5193,f116])).

fof(f116,plain,(
    ! [X4,X0] :
      ( r2_lattice3(X0,X4,sK9(X0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X4,X0)
      | v1_xboole_0(X4)
      | ~ v24_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v24_waybel_0(X0)
          | ( ! [X2] :
                ( ( ~ r3_orders_2(X0,X2,sK8(X0,X2))
                  & r2_lattice3(X0,sK7(X0),sK8(X0,X2))
                  & m1_subset_1(sK8(X0,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,sK7(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(sK7(X0),X0)
            & ~ v1_xboole_0(sK7(X0)) ) )
        & ( ! [X4] :
              ( ( ! [X6] :
                    ( r3_orders_2(X0,sK9(X0,X4),X6)
                    | ~ r2_lattice3(X0,X4,X6)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r2_lattice3(X0,X4,sK9(X0,X4))
                & m1_subset_1(sK9(X0,X4),u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_waybel_0(X4,X0)
              | v1_xboole_0(X4) )
          | ~ v24_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f69,f72,f71,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ~ r3_orders_2(X0,X2,X3)
                & r2_lattice3(X0,sK7(X0),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,sK7(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_0(sK7(X0),X0)
        & ~ v1_xboole_0(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,X2,sK8(X0,X2))
        & r2_lattice3(X0,X1,sK8(X0,X2))
        & m1_subset_1(sK8(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r3_orders_2(X0,X5,X6)
              | ~ r2_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r2_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r3_orders_2(X0,sK9(X0,X4),X6)
            | ~ r2_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r2_lattice3(X0,X4,sK9(X0,X4))
        & m1_subset_1(sK9(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v24_waybel_0(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r3_orders_2(X0,X2,X3)
                      & r2_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X4] :
              ( ? [X5] :
                  ( ! [X6] :
                      ( r3_orders_2(X0,X5,X6)
                      | ~ r2_lattice3(X0,X4,X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X4,X5)
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_waybel_0(X4,X0)
              | v1_xboole_0(X4) )
          | ~ v24_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v24_waybel_0(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r3_orders_2(X0,X2,X3)
                      & r2_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( r3_orders_2(X0,X2,X3)
                      | ~ r2_lattice3(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_waybel_0(X1,X0)
              | v1_xboole_0(X1) )
          | ~ v24_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v24_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r3_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',d39_waybel_0)).

fof(f5193,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,sK9(sK0,sK1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,X0,sK9(sK0,sK1)))
        | r1_orders_2(sK0,sK2(sK0,X0,sK9(sK0,sK1)),X1) )
    | ~ spl15_750 ),
    inference(avatar_component_clause,[],[f5192])).

fof(f5798,plain,
    ( spl15_780
    | spl15_790
    | spl15_17
    | ~ spl15_32
    | spl15_35
    | ~ spl15_40
    | ~ spl15_744 ),
    inference(avatar_split_clause,[],[f5174,f5138,f308,f283,f275,f203,f5507,f5431])).

fof(f5138,plain,
    ( spl15_744
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK0,sK2(sK0,X1,sK9(sK0,X1)),X0)
        | r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_744])])).

fof(f5174,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | ~ r2_lattice3(sK0,sK1,X0)
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_744 ),
    inference(subsumption_resolution,[],[f5173,f204])).

fof(f5173,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | ~ r2_lattice3(sK0,sK1,X0)
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK1) )
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_744 ),
    inference(subsumption_resolution,[],[f5172,f309])).

fof(f5172,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | ~ r2_lattice3(sK0,sK1,X0)
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK1) )
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_744 ),
    inference(subsumption_resolution,[],[f5168,f284])).

fof(f5168,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | ~ r2_lattice3(sK0,sK1,X0)
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0)
        | r1_yellow_0(sK0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK1) )
    | ~ spl15_32
    | ~ spl15_744 ),
    inference(resolution,[],[f5139,f276])).

fof(f5139,plain,
    ( ! [X0,X1] :
        ( ~ v1_waybel_0(X1,sK0)
        | r2_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK0,sK2(sK0,X1,sK9(sK0,X1)),X0)
        | r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(X1) )
    | ~ spl15_744 ),
    inference(avatar_component_clause,[],[f5138])).

fof(f5788,plain,
    ( spl15_826
    | ~ spl15_770
    | ~ spl15_780
    | ~ spl15_788
    | ~ spl15_794
    | ~ spl15_822 ),
    inference(avatar_split_clause,[],[f5770,f5761,f5530,f5504,f5431,f5367,f5786])).

fof(f5367,plain,
    ( spl15_770
  <=> ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK9(sK0,sK1) = X0
        | ~ r3_orders_2(sK0,X0,sK9(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_770])])).

fof(f5504,plain,
    ( spl15_788
  <=> r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_788])])).

fof(f5530,plain,
    ( spl15_794
  <=> m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_794])])).

fof(f5761,plain,
    ( spl15_822
  <=> r3_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_822])])).

fof(f5770,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK9(sK0,sK1),X0)
        | ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_770
    | ~ spl15_780
    | ~ spl15_788
    | ~ spl15_794
    | ~ spl15_822 ),
    inference(backward_demodulation,[],[f5767,f5432])).

fof(f5432,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),X0) )
    | ~ spl15_780 ),
    inference(avatar_component_clause,[],[f5431])).

fof(f5767,plain,
    ( sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1)
    | ~ spl15_770
    | ~ spl15_788
    | ~ spl15_794
    | ~ spl15_822 ),
    inference(subsumption_resolution,[],[f5766,f5505])).

fof(f5505,plain,
    ( r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_788 ),
    inference(avatar_component_clause,[],[f5504])).

fof(f5766,plain,
    ( sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_770
    | ~ spl15_794
    | ~ spl15_822 ),
    inference(subsumption_resolution,[],[f5764,f5531])).

fof(f5531,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl15_794 ),
    inference(avatar_component_clause,[],[f5530])).

fof(f5764,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_770
    | ~ spl15_822 ),
    inference(resolution,[],[f5762,f5368])).

fof(f5368,plain,
    ( ! [X0] :
        ( ~ r3_orders_2(sK0,X0,sK9(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK9(sK0,sK1) = X0
        | ~ r2_lattice3(sK0,sK1,X0) )
    | ~ spl15_770 ),
    inference(avatar_component_clause,[],[f5367])).

fof(f5762,plain,
    ( r3_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_822 ),
    inference(avatar_component_clause,[],[f5761])).

fof(f5784,plain,
    ( spl15_824
    | ~ spl15_770
    | ~ spl15_788
    | ~ spl15_794
    | ~ spl15_822 ),
    inference(avatar_split_clause,[],[f5767,f5761,f5530,f5504,f5367,f5782])).

fof(f5763,plain,
    ( spl15_822
    | ~ spl15_74
    | ~ spl15_728
    | ~ spl15_786
    | ~ spl15_794 ),
    inference(avatar_split_clause,[],[f5756,f5530,f5467,f5006,f527,f5761])).

fof(f527,plain,
    ( spl15_74
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_74])])).

fof(f5467,plain,
    ( spl15_786
  <=> r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_786])])).

fof(f5756,plain,
    ( r3_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_74
    | ~ spl15_728
    | ~ spl15_786
    | ~ spl15_794 ),
    inference(subsumption_resolution,[],[f5476,f5531])).

fof(f5476,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | r3_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_74
    | ~ spl15_728
    | ~ spl15_786 ),
    inference(subsumption_resolution,[],[f5472,f5007])).

fof(f5472,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | r3_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_74
    | ~ spl15_786 ),
    inference(resolution,[],[f5468,f528])).

fof(f528,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X1) )
    | ~ spl15_74 ),
    inference(avatar_component_clause,[],[f527])).

fof(f5468,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_786 ),
    inference(avatar_component_clause,[],[f5467])).

fof(f5653,plain,
    ( ~ spl15_791
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | spl15_17
    | ~ spl15_32
    | spl15_35
    | ~ spl15_40
    | ~ spl15_758
    | ~ spl15_782
    | spl15_795 ),
    inference(avatar_split_clause,[],[f5652,f5527,f5437,f5246,f308,f283,f275,f203,f194,f169,f155,f148,f5510])).

fof(f5246,plain,
    ( spl15_758
  <=> ! [X3] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X3,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X3)
        | ~ r2_lattice3(sK0,X3,sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_758])])).

fof(f5527,plain,
    ( spl15_795
  <=> ~ m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_795])])).

fof(f5652,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_758
    | ~ spl15_782
    | ~ spl15_795 ),
    inference(subsumption_resolution,[],[f5651,f5528])).

fof(f5528,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl15_795 ),
    inference(avatar_component_clause,[],[f5527])).

fof(f5651,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_758
    | ~ spl15_782 ),
    inference(subsumption_resolution,[],[f5261,f5438])).

fof(f5261,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_758 ),
    inference(subsumption_resolution,[],[f5260,f149])).

fof(f5260,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_758 ),
    inference(subsumption_resolution,[],[f5259,f156])).

fof(f5259,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_758 ),
    inference(subsumption_resolution,[],[f5258,f170])).

fof(f5258,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_758 ),
    inference(subsumption_resolution,[],[f5257,f195])).

fof(f5257,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_758 ),
    inference(subsumption_resolution,[],[f5256,f204])).

fof(f5256,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_758 ),
    inference(subsumption_resolution,[],[f5255,f276])).

fof(f5255,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_758 ),
    inference(subsumption_resolution,[],[f5254,f309])).

fof(f5254,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_35
    | ~ spl15_758 ),
    inference(subsumption_resolution,[],[f5253,f284])).

fof(f5253,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_758 ),
    inference(resolution,[],[f5247,f116])).

fof(f5247,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,X3,sK9(sK0,sK1))
        | ~ m1_subset_1(sK3(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X3)
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,X3,sK9(sK0,sK1)))
        | m1_subset_1(sK2(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0)) )
    | ~ spl15_758 ),
    inference(avatar_component_clause,[],[f5246])).

fof(f5650,plain,
    ( ~ spl15_6
    | spl15_35
    | ~ spl15_728
    | spl15_791
    | ~ spl15_792
    | spl15_795 ),
    inference(avatar_contradiction_clause,[],[f5649])).

fof(f5649,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_35
    | ~ spl15_728
    | ~ spl15_791
    | ~ spl15_792
    | ~ spl15_795 ),
    inference(unit_resulting_resolution,[],[f170,f284,f5007,f5522,f5511,f5528,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5609,plain,
    ( spl15_788
    | ~ spl15_6
    | spl15_35
    | ~ spl15_728
    | spl15_791
    | ~ spl15_792 ),
    inference(avatar_split_clause,[],[f5583,f5521,f5510,f5006,f283,f169,f5504])).

fof(f5583,plain,
    ( r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_6
    | ~ spl15_35
    | ~ spl15_728
    | ~ spl15_791
    | ~ spl15_792 ),
    inference(subsumption_resolution,[],[f5582,f170])).

fof(f5582,plain,
    ( r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ spl15_35
    | ~ spl15_728
    | ~ spl15_791
    | ~ spl15_792 ),
    inference(subsumption_resolution,[],[f5581,f5007])).

fof(f5581,plain,
    ( r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_35
    | ~ spl15_791
    | ~ spl15_792 ),
    inference(subsumption_resolution,[],[f5580,f5522])).

fof(f5580,plain,
    ( r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_35
    | ~ spl15_791 ),
    inference(subsumption_resolution,[],[f5578,f284])).

fof(f5578,plain,
    ( r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_791 ),
    inference(resolution,[],[f5511,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5562,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | spl15_793 ),
    inference(avatar_contradiction_clause,[],[f5561])).

fof(f5561,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_793 ),
    inference(subsumption_resolution,[],[f5560,f149])).

fof(f5560,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_793 ),
    inference(subsumption_resolution,[],[f5559,f156])).

fof(f5559,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_793 ),
    inference(subsumption_resolution,[],[f5558,f170])).

fof(f5558,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_793 ),
    inference(subsumption_resolution,[],[f5557,f195])).

fof(f5557,plain,
    ( ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_793 ),
    inference(subsumption_resolution,[],[f5556,f204])).

fof(f5556,plain,
    ( v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_793 ),
    inference(subsumption_resolution,[],[f5555,f276])).

fof(f5555,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_40
    | ~ spl15_793 ),
    inference(subsumption_resolution,[],[f5553,f309])).

fof(f5553,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_793 ),
    inference(resolution,[],[f5525,f116])).

fof(f5525,plain,
    ( ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ spl15_793 ),
    inference(avatar_component_clause,[],[f5524])).

fof(f5524,plain,
    ( spl15_793
  <=> ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_793])])).

fof(f5532,plain,
    ( ~ spl15_793
    | spl15_794
    | spl15_35
    | ~ spl15_284
    | ~ spl15_728
    | spl15_783 ),
    inference(avatar_split_clause,[],[f5516,f5434,f5006,f1553,f283,f5530,f5524])).

fof(f1553,plain,
    ( spl15_284
  <=> ! [X3,X4] :
        ( ~ r2_lattice3(sK0,X3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_subset_1(sK2(sK0,X3,X4),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X3)
        | m1_subset_1(sK3(sK0,X3,X4),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_284])])).

fof(f5516,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ spl15_35
    | ~ spl15_284
    | ~ spl15_728
    | ~ spl15_783 ),
    inference(subsumption_resolution,[],[f5515,f284])).

fof(f5515,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ spl15_284
    | ~ spl15_728
    | ~ spl15_783 ),
    inference(subsumption_resolution,[],[f5513,f5007])).

fof(f5513,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ spl15_284
    | ~ spl15_783 ),
    inference(resolution,[],[f5435,f1554])).

fof(f1554,plain,
    ( ! [X4,X3] :
        ( m1_subset_1(sK3(sK0,X3,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_subset_1(sK2(sK0,X3,X4),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X3)
        | ~ r2_lattice3(sK0,X3,X4) )
    | ~ spl15_284 ),
    inference(avatar_component_clause,[],[f1553])).

fof(f5512,plain,
    ( spl15_788
    | ~ spl15_791
    | ~ spl15_783
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | spl15_17
    | ~ spl15_32
    | spl15_35
    | ~ spl15_40
    | ~ spl15_752 ),
    inference(avatar_split_clause,[],[f5232,f5214,f308,f283,f275,f203,f194,f169,f155,f148,f5434,f5510,f5504])).

fof(f5214,plain,
    ( spl15_752
  <=> ! [X2] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X2,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X2,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X2)
        | ~ r2_lattice3(sK0,X2,sK9(sK0,sK1))
        | r2_lattice3(sK0,X2,sK2(sK0,X2,sK9(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_752])])).

fof(f5232,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_752 ),
    inference(subsumption_resolution,[],[f5231,f149])).

fof(f5231,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_752 ),
    inference(subsumption_resolution,[],[f5230,f156])).

fof(f5230,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_752 ),
    inference(subsumption_resolution,[],[f5229,f170])).

fof(f5229,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_752 ),
    inference(subsumption_resolution,[],[f5228,f195])).

fof(f5228,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_752 ),
    inference(subsumption_resolution,[],[f5227,f204])).

fof(f5227,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_32
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_752 ),
    inference(subsumption_resolution,[],[f5226,f276])).

fof(f5226,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_35
    | ~ spl15_40
    | ~ spl15_752 ),
    inference(subsumption_resolution,[],[f5225,f309])).

fof(f5225,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_35
    | ~ spl15_752 ),
    inference(subsumption_resolution,[],[f5224,f284])).

fof(f5224,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_752 ),
    inference(resolution,[],[f5215,f116])).

fof(f5215,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,X2,sK9(sK0,sK1))
        | ~ m1_subset_1(sK3(sK0,X2,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X2)
        | ~ r2_lattice3(sK0,sK1,sK3(sK0,X2,sK9(sK0,sK1)))
        | r2_lattice3(sK0,X2,sK2(sK0,X2,sK9(sK0,sK1))) )
    | ~ spl15_752 ),
    inference(avatar_component_clause,[],[f5214])).

fof(f5469,plain,
    ( spl15_786
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_728
    | ~ spl15_780 ),
    inference(avatar_split_clause,[],[f5462,f5431,f5006,f308,f275,f203,f194,f169,f155,f148,f5467])).

fof(f5462,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_728
    | ~ spl15_780 ),
    inference(subsumption_resolution,[],[f5461,f149])).

fof(f5461,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_728
    | ~ spl15_780 ),
    inference(subsumption_resolution,[],[f5460,f156])).

fof(f5460,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_728
    | ~ spl15_780 ),
    inference(subsumption_resolution,[],[f5459,f170])).

fof(f5459,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_728
    | ~ spl15_780 ),
    inference(subsumption_resolution,[],[f5458,f195])).

fof(f5458,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_728
    | ~ spl15_780 ),
    inference(subsumption_resolution,[],[f5457,f204])).

fof(f5457,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_728
    | ~ spl15_780 ),
    inference(subsumption_resolution,[],[f5456,f276])).

fof(f5456,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_40
    | ~ spl15_728
    | ~ spl15_780 ),
    inference(subsumption_resolution,[],[f5455,f309])).

fof(f5455,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_728
    | ~ spl15_780 ),
    inference(subsumption_resolution,[],[f5448,f5007])).

fof(f5448,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_780 ),
    inference(resolution,[],[f5432,f116])).

fof(f5369,plain,
    ( spl15_770
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_726
    | ~ spl15_728 ),
    inference(avatar_split_clause,[],[f5047,f5006,f5003,f169,f155,f148,f5367])).

fof(f5003,plain,
    ( spl15_726
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,X0,sK9(sK0,sK1))
        | sK9(sK0,sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_726])])).

fof(f5047,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK9(sK0,sK1) = X0
        | ~ r3_orders_2(sK0,X0,sK9(sK0,sK1)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_726
    | ~ spl15_728 ),
    inference(subsumption_resolution,[],[f5046,f149])).

fof(f5046,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK9(sK0,sK1) = X0
        | ~ r3_orders_2(sK0,X0,sK9(sK0,sK1))
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_726
    | ~ spl15_728 ),
    inference(subsumption_resolution,[],[f5045,f156])).

fof(f5045,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK9(sK0,sK1) = X0
        | ~ r3_orders_2(sK0,X0,sK9(sK0,sK1))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_726
    | ~ spl15_728 ),
    inference(subsumption_resolution,[],[f5044,f170])).

fof(f5044,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK9(sK0,sK1) = X0
        | ~ r3_orders_2(sK0,X0,sK9(sK0,sK1))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_726
    | ~ spl15_728 ),
    inference(subsumption_resolution,[],[f5041,f5007])).

fof(f5041,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK9(sK0,sK1) = X0
        | ~ r3_orders_2(sK0,X0,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_726 ),
    inference(duplicate_literal_removal,[],[f5040])).

fof(f5040,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK9(sK0,sK1) = X0
        | ~ r3_orders_2(sK0,X0,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_726 ),
    inference(resolution,[],[f5004,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',redefinition_r3_orders_2)).

fof(f5004,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK9(sK0,sK1))
        | ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK9(sK0,sK1) = X0 )
    | ~ spl15_726 ),
    inference(avatar_component_clause,[],[f5003])).

fof(f5248,plain,
    ( spl15_758
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_668
    | ~ spl15_728 ),
    inference(avatar_split_clause,[],[f5237,f5006,f4499,f169,f155,f148,f5246])).

fof(f4499,plain,
    ( spl15_668
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X0)
        | r3_orders_2(sK0,sK9(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_668])])).

fof(f5237,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X3,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X3)
        | ~ r2_lattice3(sK0,X3,sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_668
    | ~ spl15_728 ),
    inference(subsumption_resolution,[],[f4515,f5007])).

fof(f4515,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X3,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X3)
        | ~ r2_lattice3(sK0,X3,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | m1_subset_1(sK2(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_668 ),
    inference(subsumption_resolution,[],[f4514,f149])).

fof(f4514,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X3,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X3)
        | ~ r2_lattice3(sK0,X3,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | m1_subset_1(sK2(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_668 ),
    inference(subsumption_resolution,[],[f4513,f156])).

fof(f4513,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X3,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X3)
        | ~ r2_lattice3(sK0,X3,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | m1_subset_1(sK2(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_668 ),
    inference(subsumption_resolution,[],[f4505,f170])).

fof(f4505,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X3,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X3)
        | ~ r2_lattice3(sK0,X3,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | m1_subset_1(sK2(sK0,X3,sK9(sK0,sK1)),u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_668 ),
    inference(resolution,[],[f4500,f397])).

fof(f397,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X2,sK3(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f396,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f396,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f395])).

fof(f395,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f102,f134])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f4500,plain,
    ( ! [X0] :
        ( r3_orders_2(sK0,sK9(sK0,sK1),X0)
        | ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_668 ),
    inference(avatar_component_clause,[],[f4499])).

fof(f5216,plain,
    ( spl15_752
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_668
    | ~ spl15_728 ),
    inference(avatar_split_clause,[],[f5209,f5006,f4499,f169,f155,f148,f5214])).

fof(f5209,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X2,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X2,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X2)
        | ~ r2_lattice3(sK0,X2,sK9(sK0,sK1))
        | r2_lattice3(sK0,X2,sK2(sK0,X2,sK9(sK0,sK1))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_668
    | ~ spl15_728 ),
    inference(subsumption_resolution,[],[f4512,f5007])).

fof(f4512,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X2,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X2,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X2)
        | ~ r2_lattice3(sK0,X2,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | r2_lattice3(sK0,X2,sK2(sK0,X2,sK9(sK0,sK1))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_668 ),
    inference(subsumption_resolution,[],[f4511,f149])).

fof(f4511,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X2,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X2,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X2)
        | ~ r2_lattice3(sK0,X2,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | r2_lattice3(sK0,X2,sK2(sK0,X2,sK9(sK0,sK1)))
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_668 ),
    inference(subsumption_resolution,[],[f4510,f156])).

fof(f4510,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X2,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X2,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X2)
        | ~ r2_lattice3(sK0,X2,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | r2_lattice3(sK0,X2,sK2(sK0,X2,sK9(sK0,sK1)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_668 ),
    inference(subsumption_resolution,[],[f4504,f170])).

fof(f4504,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X2,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X2,sK9(sK0,sK1)),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X2)
        | ~ r2_lattice3(sK0,X2,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_lattice3(sK0,X2,sK2(sK0,X2,sK9(sK0,sK1)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_668 ),
    inference(resolution,[],[f4500,f407])).

fof(f407,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X2,sK3(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f406,f103])).

fof(f406,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f405])).

fof(f405,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f105,f134])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5194,plain,
    ( spl15_750
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_92
    | ~ spl15_668
    | ~ spl15_728 ),
    inference(avatar_split_clause,[],[f5188,f5006,f4499,f606,f169,f155,f148,f5192])).

fof(f606,plain,
    ( spl15_92
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(sK0,sK2(sK0,X0,X1),X2)
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_92])])).

fof(f5188,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X0,sK9(sK0,sK1)))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK9(sK0,sK1))
        | r1_orders_2(sK0,sK2(sK0,X0,sK9(sK0,sK1)),X1) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_92
    | ~ spl15_668
    | ~ spl15_728 ),
    inference(subsumption_resolution,[],[f4509,f5007])).

fof(f4509,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X0,sK9(sK0,sK1)))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,X0,sK9(sK0,sK1)),X1) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_92
    | ~ spl15_668 ),
    inference(subsumption_resolution,[],[f4508,f607])).

fof(f607,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,sK2(sK0,X0,X1),X2)
        | r1_yellow_0(sK0,X0) )
    | ~ spl15_92 ),
    inference(avatar_component_clause,[],[f606])).

fof(f4508,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X0,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X0,sK9(sK0,sK1)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,X0,sK9(sK0,sK1)),X1) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_668 ),
    inference(subsumption_resolution,[],[f4507,f149])).

fof(f4507,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X0,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X0,sK9(sK0,sK1)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,X0,sK9(sK0,sK1)),X1)
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_668 ),
    inference(subsumption_resolution,[],[f4506,f156])).

fof(f4506,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X0,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X0,sK9(sK0,sK1)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,X0,sK9(sK0,sK1)),X1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_668 ),
    inference(subsumption_resolution,[],[f4503,f170])).

fof(f4503,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,sK1,sK3(sK0,X0,sK9(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,X0,sK9(sK0,sK1)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,sK2(sK0,X0,sK9(sK0,sK1)),X1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_668 ),
    inference(resolution,[],[f4500,f423])).

fof(f423,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK2(X0,X1,X2),X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f422,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK2(X0,X1,X2),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f422,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK2(X0,X1,X2),X3)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f421])).

fof(f421,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK2(X0,X1,X2),X3)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f108,f134])).

fof(f108,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | r1_orders_2(X0,sK2(X0,X1,X2),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f5140,plain,
    ( spl15_744
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_680 ),
    inference(avatar_split_clause,[],[f4611,f4596,f194,f169,f155,f148,f5138])).

fof(f4596,plain,
    ( spl15_680
  <=> ! [X9,X7,X8] :
        ( ~ r2_lattice3(sK0,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_lattice3(sK0,X7,sK3(sK0,X7,sK9(sK0,X9)))
        | ~ r2_lattice3(sK0,X7,sK9(sK0,X9))
        | r1_orders_2(sK0,sK2(sK0,X7,sK9(sK0,X9)),X8)
        | r1_yellow_0(sK0,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X9,sK0)
        | v1_xboole_0(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_680])])).

fof(f4611,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK0,sK2(sK0,X1,sK9(sK0,X1)),X0)
        | r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_680 ),
    inference(subsumption_resolution,[],[f4610,f149])).

fof(f4610,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK0,sK2(sK0,X1,sK9(sK0,X1)),X0)
        | r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_680 ),
    inference(subsumption_resolution,[],[f4609,f156])).

fof(f4609,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK0,sK2(sK0,X1,sK9(sK0,X1)),X0)
        | r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_680 ),
    inference(subsumption_resolution,[],[f4608,f170])).

fof(f4608,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK0,sK2(sK0,X1,sK9(sK0,X1)),X0)
        | r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_14
    | ~ spl15_680 ),
    inference(subsumption_resolution,[],[f4607,f195])).

fof(f4607,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK0,sK2(sK0,X1,sK9(sK0,X1)),X0)
        | r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | ~ v24_waybel_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_680 ),
    inference(duplicate_literal_removal,[],[f4606])).

fof(f4606,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK0,sK2(sK0,X1,sK9(sK0,X1)),X0)
        | r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | ~ v24_waybel_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_680 ),
    inference(resolution,[],[f4597,f116])).

fof(f4597,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_lattice3(sK0,X7,sK9(sK0,X9))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_lattice3(sK0,X7,sK3(sK0,X7,sK9(sK0,X9)))
        | ~ r2_lattice3(sK0,X7,X8)
        | r1_orders_2(sK0,sK2(sK0,X7,sK9(sK0,X9)),X8)
        | r1_yellow_0(sK0,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X9,sK0)
        | v1_xboole_0(X9) )
    | ~ spl15_680 ),
    inference(avatar_component_clause,[],[f4596])).

fof(f5030,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | spl15_729 ),
    inference(avatar_contradiction_clause,[],[f5029])).

fof(f5029,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_729 ),
    inference(subsumption_resolution,[],[f5028,f149])).

fof(f5028,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_729 ),
    inference(subsumption_resolution,[],[f5027,f156])).

fof(f5027,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_729 ),
    inference(subsumption_resolution,[],[f5026,f170])).

fof(f5026,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_729 ),
    inference(subsumption_resolution,[],[f5025,f195])).

fof(f5025,plain,
    ( ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_729 ),
    inference(subsumption_resolution,[],[f5024,f204])).

fof(f5024,plain,
    ( v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_729 ),
    inference(subsumption_resolution,[],[f5023,f276])).

fof(f5023,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_40
    | ~ spl15_729 ),
    inference(subsumption_resolution,[],[f5016,f309])).

fof(f5016,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_729 ),
    inference(resolution,[],[f5010,f115])).

fof(f115,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK9(X0,X4),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X4,X0)
      | v1_xboole_0(X4)
      | ~ v24_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f5010,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl15_729 ),
    inference(avatar_component_clause,[],[f5009])).

fof(f5009,plain,
    ( spl15_729
  <=> ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_729])])).

fof(f5011,plain,
    ( spl15_726
    | ~ spl15_729
    | ~ spl15_128
    | ~ spl15_668 ),
    inference(avatar_split_clause,[],[f4519,f4499,f802,f5009,f5003])).

fof(f802,plain,
    ( spl15_128
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r3_orders_2(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_128])])).

fof(f4519,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK9(sK0,sK1) = X0
        | ~ r1_orders_2(sK0,X0,sK9(sK0,sK1))
        | ~ r2_lattice3(sK0,sK1,X0) )
    | ~ spl15_128
    | ~ spl15_668 ),
    inference(duplicate_literal_removal,[],[f4516])).

fof(f4516,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK9(sK0,sK1) = X0
        | ~ r1_orders_2(sK0,X0,sK9(sK0,sK1))
        | ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_128
    | ~ spl15_668 ),
    inference(resolution,[],[f803,f4500])).

fof(f803,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl15_128 ),
    inference(avatar_component_clause,[],[f802])).

fof(f4598,plain,
    ( spl15_680
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_96 ),
    inference(avatar_split_clause,[],[f4429,f617,f194,f169,f155,f148,f4596])).

fof(f617,plain,
    ( spl15_96
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(sK0,sK2(sK0,X0,X1),X2)
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK3(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_96])])).

fof(f4429,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_lattice3(sK0,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_lattice3(sK0,X7,sK3(sK0,X7,sK9(sK0,X9)))
        | ~ r2_lattice3(sK0,X7,sK9(sK0,X9))
        | r1_orders_2(sK0,sK2(sK0,X7,sK9(sK0,X9)),X8)
        | r1_yellow_0(sK0,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X9,sK0)
        | v1_xboole_0(X9) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_96 ),
    inference(subsumption_resolution,[],[f4428,f149])).

fof(f4428,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_lattice3(sK0,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_lattice3(sK0,X7,sK3(sK0,X7,sK9(sK0,X9)))
        | ~ r2_lattice3(sK0,X7,sK9(sK0,X9))
        | r1_orders_2(sK0,sK2(sK0,X7,sK9(sK0,X9)),X8)
        | r1_yellow_0(sK0,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X9,sK0)
        | v1_xboole_0(X9)
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_96 ),
    inference(subsumption_resolution,[],[f4427,f156])).

fof(f4427,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_lattice3(sK0,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_lattice3(sK0,X7,sK3(sK0,X7,sK9(sK0,X9)))
        | ~ r2_lattice3(sK0,X7,sK9(sK0,X9))
        | r1_orders_2(sK0,sK2(sK0,X7,sK9(sK0,X9)),X8)
        | r1_yellow_0(sK0,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X9,sK0)
        | v1_xboole_0(X9)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_96 ),
    inference(subsumption_resolution,[],[f4426,f170])).

fof(f4426,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_lattice3(sK0,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_lattice3(sK0,X7,sK3(sK0,X7,sK9(sK0,X9)))
        | ~ r2_lattice3(sK0,X7,sK9(sK0,X9))
        | r1_orders_2(sK0,sK2(sK0,X7,sK9(sK0,X9)),X8)
        | r1_yellow_0(sK0,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X9,sK0)
        | v1_xboole_0(X9)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_14
    | ~ spl15_96 ),
    inference(subsumption_resolution,[],[f4420,f195])).

fof(f4420,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_lattice3(sK0,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_lattice3(sK0,X7,sK3(sK0,X7,sK9(sK0,X9)))
        | ~ r2_lattice3(sK0,X7,sK9(sK0,X9))
        | r1_orders_2(sK0,sK2(sK0,X7,sK9(sK0,X9)),X8)
        | r1_yellow_0(sK0,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X9,sK0)
        | v1_xboole_0(X9)
        | ~ v24_waybel_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_96 ),
    inference(resolution,[],[f618,f115])).

fof(f618,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK3(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,sK2(sK0,X0,X1),X2)
        | r1_yellow_0(sK0,X0) )
    | ~ spl15_96 ),
    inference(avatar_component_clause,[],[f617])).

fof(f4501,plain,
    ( spl15_668
    | spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_660 ),
    inference(avatar_split_clause,[],[f4398,f4390,f308,f275,f203,f4499])).

fof(f4390,plain,
    ( spl15_660
  <=> ! [X1,X2] :
        ( ~ r2_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | r3_orders_2(sK0,sK9(sK0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_660])])).

fof(f4398,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X0)
        | r3_orders_2(sK0,sK9(sK0,sK1),X0) )
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f4397,f204])).

fof(f4397,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X0)
        | v1_xboole_0(sK1)
        | r3_orders_2(sK0,sK9(sK0,sK1),X0) )
    | ~ spl15_32
    | ~ spl15_40
    | ~ spl15_660 ),
    inference(subsumption_resolution,[],[f4393,f309])).

fof(f4393,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_lattice3(sK0,sK1,X0)
        | v1_xboole_0(sK1)
        | r3_orders_2(sK0,sK9(sK0,sK1),X0) )
    | ~ spl15_32
    | ~ spl15_660 ),
    inference(resolution,[],[f4391,f276])).

fof(f4391,plain,
    ( ! [X2,X1] :
        ( ~ v1_waybel_0(X1,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_lattice3(sK0,X1,X2)
        | v1_xboole_0(X1)
        | r3_orders_2(sK0,sK9(sK0,X1),X2) )
    | ~ spl15_660 ),
    inference(avatar_component_clause,[],[f4390])).

fof(f4392,plain,
    ( spl15_660
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f4339,f194,f169,f155,f148,f4390])).

fof(f4339,plain,
    ( ! [X2,X1] :
        ( ~ r2_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | r3_orders_2(sK0,sK9(sK0,X1),X2) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f4338,f149])).

fof(f4338,plain,
    ( ! [X2,X1] :
        ( ~ r2_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | r3_orders_2(sK0,sK9(sK0,X1),X2)
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f4337,f156])).

fof(f4337,plain,
    ( ! [X2,X1] :
        ( ~ r2_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | r3_orders_2(sK0,sK9(sK0,X1),X2)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f4333,f170])).

fof(f4333,plain,
    ( ! [X2,X1] :
        ( ~ r2_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | r3_orders_2(sK0,sK9(sK0,X1),X2)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_14 ),
    inference(resolution,[],[f195,f117])).

fof(f117,plain,(
    ! [X6,X4,X0] :
      ( ~ v24_waybel_0(X0)
      | ~ r2_lattice3(X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X4,X0)
      | v1_xboole_0(X4)
      | r3_orders_2(X0,sK9(X0,X4),X6)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f4353,plain,
    ( ~ spl15_138
    | spl15_647 ),
    inference(avatar_contradiction_clause,[],[f4352])).

fof(f4352,plain,
    ( $false
    | ~ spl15_138
    | ~ spl15_647 ),
    inference(unit_resulting_resolution,[],[f856,f4243,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',t3_subset)).

fof(f4243,plain,
    ( ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl15_647 ),
    inference(avatar_component_clause,[],[f4242])).

fof(f4242,plain,
    ( spl15_647
  <=> ~ m1_subset_1(sK7(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_647])])).

fof(f856,plain,
    ( r1_tarski(sK7(sK0),o_0_0_xboole_0)
    | ~ spl15_138 ),
    inference(avatar_component_clause,[],[f855])).

fof(f855,plain,
    ( spl15_138
  <=> r1_tarski(sK7(sK0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_138])])).

fof(f4287,plain,
    ( spl15_104
    | ~ spl15_652 ),
    inference(avatar_split_clause,[],[f4276,f4269,f675])).

fof(f675,plain,
    ( spl15_104
  <=> v1_xboole_0(sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_104])])).

fof(f4269,plain,
    ( spl15_652
  <=> ! [X0] : ~ r2_hidden(X0,sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_652])])).

fof(f4276,plain,
    ( v1_xboole_0(sK7(sK0))
    | ~ spl15_652 ),
    inference(resolution,[],[f4270,f225])).

fof(f4270,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK7(sK0))
    | ~ spl15_652 ),
    inference(avatar_component_clause,[],[f4269])).

fof(f4271,plain,
    ( spl15_652
    | ~ spl15_648 ),
    inference(avatar_split_clause,[],[f4266,f4259,f4269])).

fof(f4259,plain,
    ( spl15_648
  <=> sP14(sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_648])])).

fof(f4266,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK7(sK0))
    | ~ spl15_648 ),
    inference(resolution,[],[f4260,f143])).

fof(f4260,plain,
    ( sP14(sK7(sK0))
    | ~ spl15_648 ),
    inference(avatar_component_clause,[],[f4259])).

fof(f4261,plain,
    ( spl15_648
    | ~ spl15_22
    | ~ spl15_646 ),
    inference(avatar_split_clause,[],[f4249,f4245,f232,f4259])).

fof(f4245,plain,
    ( spl15_646
  <=> m1_subset_1(sK7(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_646])])).

fof(f4249,plain,
    ( sP14(sK7(sK0))
    | ~ spl15_22
    | ~ spl15_646 ),
    inference(resolution,[],[f4246,f233])).

fof(f4246,plain,
    ( m1_subset_1(sK7(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl15_646 ),
    inference(avatar_component_clause,[],[f4245])).

fof(f3997,plain,
    ( ~ spl15_631
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | spl15_15
    | ~ spl15_194
    | spl15_635 ),
    inference(avatar_split_clause,[],[f3996,f3917,f1194,f197,f169,f155,f148,f3905])).

fof(f3905,plain,
    ( spl15_631
  <=> ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_631])])).

fof(f197,plain,
    ( spl15_15
  <=> ~ v24_waybel_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f1194,plain,
    ( spl15_194
  <=> m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_194])])).

fof(f3917,plain,
    ( spl15_635
  <=> ~ r2_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_635])])).

fof(f3996,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_194
    | ~ spl15_635 ),
    inference(subsumption_resolution,[],[f3995,f149])).

fof(f3995,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_194
    | ~ spl15_635 ),
    inference(subsumption_resolution,[],[f3994,f156])).

fof(f3994,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_194
    | ~ spl15_635 ),
    inference(subsumption_resolution,[],[f3993,f170])).

fof(f3993,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_15
    | ~ spl15_194
    | ~ spl15_635 ),
    inference(subsumption_resolution,[],[f3992,f1195])).

fof(f1195,plain,
    ( m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ spl15_194 ),
    inference(avatar_component_clause,[],[f1194])).

fof(f3992,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_15
    | ~ spl15_635 ),
    inference(subsumption_resolution,[],[f3991,f198])).

fof(f198,plain,
    ( ~ v24_waybel_0(sK0)
    | ~ spl15_15 ),
    inference(avatar_component_clause,[],[f197])).

fof(f3991,plain,
    ( v24_waybel_0(sK0)
    | ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_635 ),
    inference(resolution,[],[f3918,f122])).

fof(f122,plain,(
    ! [X2,X0] :
      ( r2_lattice3(X0,sK7(X0),sK8(X0,X2))
      | v24_waybel_0(X0)
      | ~ r2_lattice3(X0,sK7(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f3918,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ spl15_635 ),
    inference(avatar_component_clause,[],[f3917])).

fof(f3985,plain,
    ( ~ spl15_631
    | ~ spl15_194
    | ~ spl15_254
    | spl15_633 ),
    inference(avatar_split_clause,[],[f3938,f3911,f1440,f1194,f3905])).

fof(f1440,plain,
    ( spl15_254
  <=> ! [X2] :
        ( ~ r2_lattice3(sK0,sK7(sK0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK8(sK0,X2),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_254])])).

fof(f3911,plain,
    ( spl15_633
  <=> ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_633])])).

fof(f3938,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ spl15_194
    | ~ spl15_254
    | ~ spl15_633 ),
    inference(subsumption_resolution,[],[f3936,f1195])).

fof(f3936,plain,
    ( ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ spl15_254
    | ~ spl15_633 ),
    inference(resolution,[],[f3912,f1441])).

fof(f1441,plain,
    ( ! [X2] :
        ( m1_subset_1(sK8(sK0,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK7(sK0),X2) )
    | ~ spl15_254 ),
    inference(avatar_component_clause,[],[f1440])).

fof(f3912,plain,
    ( ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ spl15_633 ),
    inference(avatar_component_clause,[],[f3911])).

fof(f3932,plain,
    ( ~ spl15_6
    | ~ spl15_116
    | spl15_631 ),
    inference(avatar_contradiction_clause,[],[f3931])).

fof(f3931,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_116
    | ~ spl15_631 ),
    inference(subsumption_resolution,[],[f3930,f170])).

fof(f3930,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl15_116
    | ~ spl15_631 ),
    inference(subsumption_resolution,[],[f3928,f728])).

fof(f728,plain,
    ( r1_yellow_0(sK0,sK7(sK0))
    | ~ spl15_116 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl15_116
  <=> r1_yellow_0(sK0,sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_116])])).

fof(f3928,plain,
    ( ~ r1_yellow_0(sK0,sK7(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_631 ),
    inference(resolution,[],[f3906,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK4(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f3906,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ spl15_631 ),
    inference(avatar_component_clause,[],[f3905])).

fof(f3919,plain,
    ( ~ spl15_631
    | ~ spl15_633
    | ~ spl15_635
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | spl15_15
    | ~ spl15_194
    | ~ spl15_372 ),
    inference(avatar_split_clause,[],[f2210,f2136,f1194,f197,f169,f155,f148,f3917,f3911,f3905])).

fof(f2136,plain,
    ( spl15_372
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK7(sK0),X1)
        | r3_orders_2(sK0,sK4(sK0,sK7(sK0)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_372])])).

fof(f2210,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_194
    | ~ spl15_372 ),
    inference(subsumption_resolution,[],[f2209,f149])).

fof(f2209,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_194
    | ~ spl15_372 ),
    inference(subsumption_resolution,[],[f2208,f156])).

fof(f2208,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_194
    | ~ spl15_372 ),
    inference(subsumption_resolution,[],[f2207,f170])).

fof(f2207,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_15
    | ~ spl15_194
    | ~ spl15_372 ),
    inference(subsumption_resolution,[],[f2206,f1195])).

fof(f2206,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_15
    | ~ spl15_372 ),
    inference(subsumption_resolution,[],[f2200,f198])).

fof(f2200,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | v24_waybel_0(sK0)
    | ~ r2_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_372 ),
    inference(resolution,[],[f2137,f123])).

fof(f123,plain,(
    ! [X2,X0] :
      ( ~ r3_orders_2(X0,X2,sK8(X0,X2))
      | v24_waybel_0(X0)
      | ~ r2_lattice3(X0,sK7(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f2137,plain,
    ( ! [X1] :
        ( r3_orders_2(sK0,sK4(sK0,sK7(sK0)),X1)
        | ~ r2_lattice3(sK0,sK7(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl15_372 ),
    inference(avatar_component_clause,[],[f2136])).

fof(f2168,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | spl15_15
    | ~ spl15_104 ),
    inference(avatar_contradiction_clause,[],[f2167])).

fof(f2167,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_104 ),
    inference(subsumption_resolution,[],[f2166,f149])).

fof(f2166,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_104 ),
    inference(subsumption_resolution,[],[f2165,f156])).

fof(f2165,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_104 ),
    inference(subsumption_resolution,[],[f2164,f170])).

fof(f2164,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_15
    | ~ spl15_104 ),
    inference(subsumption_resolution,[],[f2159,f198])).

fof(f2159,plain,
    ( v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_104 ),
    inference(resolution,[],[f676,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK7(X0))
      | v24_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f676,plain,
    ( v1_xboole_0(sK7(sK0))
    | ~ spl15_104 ),
    inference(avatar_component_clause,[],[f675])).

fof(f2138,plain,
    ( spl15_372
    | ~ spl15_74
    | ~ spl15_194
    | ~ spl15_264 ),
    inference(avatar_split_clause,[],[f1489,f1476,f1194,f527,f2136])).

fof(f1476,plain,
    ( spl15_264
  <=> ! [X3] :
        ( ~ r2_lattice3(sK0,sK7(sK0),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK4(sK0,sK7(sK0)),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_264])])).

fof(f1489,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK7(sK0),X1)
        | r3_orders_2(sK0,sK4(sK0,sK7(sK0)),X1) )
    | ~ spl15_74
    | ~ spl15_194
    | ~ spl15_264 ),
    inference(subsumption_resolution,[],[f1486,f1195])).

fof(f1486,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK7(sK0),X1)
        | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
        | r3_orders_2(sK0,sK4(sK0,sK7(sK0)),X1) )
    | ~ spl15_74
    | ~ spl15_264 ),
    inference(duplicate_literal_removal,[],[f1482])).

fof(f1482,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK7(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
        | r3_orders_2(sK0,sK4(sK0,sK7(sK0)),X1) )
    | ~ spl15_74
    | ~ spl15_264 ),
    inference(resolution,[],[f1477,f528])).

fof(f1477,plain,
    ( ! [X3] :
        ( r1_orders_2(sK0,sK4(sK0,sK7(sK0)),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK7(sK0),X3) )
    | ~ spl15_264 ),
    inference(avatar_component_clause,[],[f1476])).

fof(f1555,plain,
    ( spl15_284
    | ~ spl15_166 ),
    inference(avatar_split_clause,[],[f1095,f1090,f1553])).

fof(f1090,plain,
    ( spl15_166
  <=> ! [X1,X0] :
        ( r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,X0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_166])])).

fof(f1095,plain,
    ( ! [X4,X3] :
        ( ~ r2_lattice3(sK0,X3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_subset_1(sK2(sK0,X3,X4),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X3)
        | m1_subset_1(sK3(sK0,X3,X4),u1_struct_0(sK0)) )
    | ~ spl15_166 ),
    inference(resolution,[],[f1091,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',t1_subset)).

fof(f1091,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl15_166 ),
    inference(avatar_component_clause,[],[f1090])).

fof(f1478,plain,
    ( spl15_264
    | ~ spl15_6
    | ~ spl15_116 ),
    inference(avatar_split_clause,[],[f746,f727,f169,f1476])).

fof(f746,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,sK7(sK0),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK4(sK0,sK7(sK0)),X3) )
    | ~ spl15_6
    | ~ spl15_116 ),
    inference(subsumption_resolution,[],[f741,f170])).

fof(f741,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,sK7(sK0),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK4(sK0,sK7(sK0)),X3)
        | ~ l1_orders_2(sK0) )
    | ~ spl15_116 ),
    inference(resolution,[],[f728,f96])).

fof(f96,plain,(
    ! [X0,X1,X9] :
      ( ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | r1_orders_2(X0,sK4(X0,X1),X9)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1442,plain,
    ( spl15_254
    | ~ spl15_126 ),
    inference(avatar_split_clause,[],[f924,f795,f1440])).

fof(f795,plain,
    ( spl15_126
  <=> ! [X0] :
        ( ~ r2_lattice3(sK0,sK7(sK0),X0)
        | r2_hidden(sK8(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_126])])).

fof(f924,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,sK7(sK0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK8(sK0,X2),u1_struct_0(sK0)) )
    | ~ spl15_126 ),
    inference(resolution,[],[f796,f127])).

fof(f796,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK0,X0),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK7(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_126 ),
    inference(avatar_component_clause,[],[f795])).

fof(f1196,plain,
    ( spl15_194
    | ~ spl15_6
    | ~ spl15_116 ),
    inference(avatar_split_clause,[],[f747,f727,f169,f1194])).

fof(f747,plain,
    ( m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ spl15_6
    | ~ spl15_116 ),
    inference(subsumption_resolution,[],[f742,f170])).

fof(f742,plain,
    ( m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_116 ),
    inference(resolution,[],[f728,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1092,plain,
    ( spl15_166
    | ~ spl15_6
    | spl15_125 ),
    inference(avatar_split_clause,[],[f1084,f789,f169,f1090])).

fof(f789,plain,
    ( spl15_125
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_125])])).

fof(f1084,plain,
    ( ! [X0,X1] :
        ( r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,X0,X1),u1_struct_0(sK0)) )
    | ~ spl15_6
    | ~ spl15_125 ),
    inference(subsumption_resolution,[],[f585,f790])).

fof(f790,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_125 ),
    inference(avatar_component_clause,[],[f789])).

fof(f585,plain,
    ( ! [X0,X1] :
        ( r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,X0,X1),u1_struct_0(sK0)) )
    | ~ spl15_6 ),
    inference(resolution,[],[f390,f170])).

fof(f390,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X0))
      | r2_hidden(sK3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f100,f128])).

fof(f857,plain,
    ( spl15_138
    | ~ spl15_20
    | ~ spl15_64
    | ~ spl15_124 ),
    inference(avatar_split_clause,[],[f809,f792,f479,f216,f855])).

fof(f216,plain,
    ( spl15_20
  <=> ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f479,plain,
    ( spl15_64
  <=> r1_tarski(sK7(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_64])])).

fof(f792,plain,
    ( spl15_124
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_124])])).

fof(f809,plain,
    ( r1_tarski(sK7(sK0),o_0_0_xboole_0)
    | ~ spl15_20
    | ~ spl15_64
    | ~ spl15_124 ),
    inference(backward_demodulation,[],[f800,f480])).

fof(f480,plain,
    ( r1_tarski(sK7(sK0),u1_struct_0(sK0))
    | ~ spl15_64 ),
    inference(avatar_component_clause,[],[f479])).

fof(f800,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl15_20
    | ~ spl15_124 ),
    inference(resolution,[],[f793,f217])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl15_20 ),
    inference(avatar_component_clause,[],[f216])).

fof(f793,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_124 ),
    inference(avatar_component_clause,[],[f792])).

fof(f831,plain,
    ( spl15_130
    | ~ spl15_20
    | ~ spl15_124 ),
    inference(avatar_split_clause,[],[f800,f792,f216,f829])).

fof(f804,plain,
    ( spl15_128
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_84 ),
    inference(avatar_split_clause,[],[f571,f560,f169,f155,f148,f802])).

fof(f560,plain,
    ( spl15_84
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_84])])).

fof(f571,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r3_orders_2(sK0,X1,X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_84 ),
    inference(subsumption_resolution,[],[f570,f149])).

fof(f570,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r3_orders_2(sK0,X1,X0)
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_84 ),
    inference(subsumption_resolution,[],[f569,f156])).

fof(f569,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r3_orders_2(sK0,X1,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_84 ),
    inference(subsumption_resolution,[],[f568,f170])).

fof(f568,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r3_orders_2(sK0,X1,X0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_84 ),
    inference(duplicate_literal_removal,[],[f567])).

fof(f567,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_84 ),
    inference(resolution,[],[f561,f134])).

fof(f561,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | X0 = X1 )
    | ~ spl15_84 ),
    inference(avatar_component_clause,[],[f560])).

fof(f797,plain,
    ( spl15_124
    | spl15_126
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | spl15_15 ),
    inference(avatar_split_clause,[],[f583,f197,f169,f155,f148,f795,f792])).

fof(f583,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK7(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK8(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f582,f149])).

fof(f582,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK7(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK8(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f581,f198])).

fof(f581,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK7(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v24_waybel_0(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK8(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl15_2
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f580,f170])).

fof(f580,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK7(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v24_waybel_0(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK8(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl15_2 ),
    inference(resolution,[],[f342,f156])).

fof(f342,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r2_lattice3(X0,sK7(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v24_waybel_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r2_hidden(sK8(X0,X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f121,f128])).

fof(f121,plain,(
    ! [X2,X0] :
      ( m1_subset_1(sK8(X0,X2),u1_struct_0(X0))
      | v24_waybel_0(X0)
      | ~ r2_lattice3(X0,sK7(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f737,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | spl15_15
    | spl15_115 ),
    inference(avatar_contradiction_clause,[],[f736])).

fof(f736,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_115 ),
    inference(subsumption_resolution,[],[f735,f149])).

fof(f735,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_115 ),
    inference(subsumption_resolution,[],[f734,f156])).

fof(f734,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_115 ),
    inference(subsumption_resolution,[],[f733,f170])).

fof(f733,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_15
    | ~ spl15_115 ),
    inference(subsumption_resolution,[],[f731,f198])).

fof(f731,plain,
    ( v24_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_115 ),
    inference(resolution,[],[f722,f119])).

fof(f119,plain,(
    ! [X0] :
      ( v1_waybel_0(sK7(X0),X0)
      | v24_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f722,plain,
    ( ~ v1_waybel_0(sK7(sK0),sK0)
    | ~ spl15_115 ),
    inference(avatar_component_clause,[],[f721])).

fof(f721,plain,
    ( spl15_115
  <=> ~ v1_waybel_0(sK7(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_115])])).

fof(f729,plain,
    ( spl15_104
    | ~ spl15_115
    | spl15_116
    | ~ spl15_30
    | ~ spl15_62 ),
    inference(avatar_split_clause,[],[f472,f447,f266,f727,f721,f675])).

fof(f266,plain,
    ( spl15_30
  <=> ! [X2] :
        ( r1_yellow_0(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X2,sK0)
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_30])])).

fof(f447,plain,
    ( spl15_62
  <=> m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_62])])).

fof(f472,plain,
    ( r1_yellow_0(sK0,sK7(sK0))
    | ~ v1_waybel_0(sK7(sK0),sK0)
    | v1_xboole_0(sK7(sK0))
    | ~ spl15_30
    | ~ spl15_62 ),
    inference(resolution,[],[f448,f267])).

fof(f267,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X2)
        | ~ v1_waybel_0(X2,sK0)
        | v1_xboole_0(X2) )
    | ~ spl15_30 ),
    inference(avatar_component_clause,[],[f266])).

fof(f448,plain,
    ( m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_62 ),
    inference(avatar_component_clause,[],[f447])).

fof(f619,plain,
    ( spl15_96
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f419,f169,f617])).

fof(f419,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,sK2(sK0,X0,X1),X2)
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK3(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl15_6 ),
    inference(resolution,[],[f107,f170])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK2(X0,X1,X2),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f608,plain,
    ( spl15_92
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f413,f169,f606])).

fof(f413,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,sK2(sK0,X0,X1),X2)
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl15_6 ),
    inference(resolution,[],[f106,f170])).

fof(f562,plain,
    ( spl15_84
    | ~ spl15_4
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f352,f169,f162,f560])).

fof(f162,plain,
    ( spl15_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f352,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | X0 = X1 )
    | ~ spl15_4
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f351,f170])).

fof(f351,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | X0 = X1 )
    | ~ spl15_4 ),
    inference(resolution,[],[f124,f163])).

fof(f163,plain,
    ( v5_orders_2(sK0)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',t25_orders_2)).

fof(f529,plain,
    ( spl15_74
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f334,f169,f155,f148,f527])).

fof(f334,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X1) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f333,f149])).

fof(f333,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f332,f170])).

fof(f332,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r3_orders_2(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl15_2 ),
    inference(resolution,[],[f135,f156])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r3_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f481,plain,
    ( spl15_64
    | ~ spl15_62 ),
    inference(avatar_split_clause,[],[f473,f447,f479])).

fof(f473,plain,
    ( r1_tarski(sK7(sK0),u1_struct_0(sK0))
    | ~ spl15_62 ),
    inference(resolution,[],[f448,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f449,plain,
    ( spl15_62
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | spl15_15 ),
    inference(avatar_split_clause,[],[f439,f197,f169,f155,f148,f447])).

fof(f439,plain,
    ( m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f269,f198])).

fof(f269,plain,
    ( m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v24_waybel_0(sK0)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f251,f149])).

fof(f251,plain,
    ( m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v24_waybel_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6 ),
    inference(subsumption_resolution,[],[f250,f170])).

fof(f250,plain,
    ( m1_subset_1(sK7(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v24_waybel_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_2 ),
    inference(resolution,[],[f120,f156])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v3_orders_2(X0)
      | m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v24_waybel_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f310,plain,
    ( spl15_40
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f296,f194,f308])).

fof(f296,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f89,f195])).

fof(f89,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v24_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ( ~ r1_yellow_0(sK0,sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v1_waybel_0(sK1,sK0)
        & ~ v1_xboole_0(sK1) )
      | ~ v24_waybel_0(sK0) )
    & ( ! [X2] :
          ( r1_yellow_0(sK0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v1_waybel_0(X2,sK0)
          | v1_xboole_0(X2) )
      | v24_waybel_0(sK0) )
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r1_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          | ~ v24_waybel_0(X0) )
        & ( ! [X2] :
              ( r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | v24_waybel_0(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ~ r1_yellow_0(sK0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & v1_waybel_0(X1,sK0)
            & ~ v1_xboole_0(X1) )
        | ~ v24_waybel_0(sK0) )
      & ( ! [X2] :
            ( r1_yellow_0(sK0,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v1_waybel_0(X2,sK0)
            | v1_xboole_0(X2) )
        | v24_waybel_0(sK0) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ~ r1_yellow_0(X0,sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_0(sK1,X0)
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r1_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        | ~ v24_waybel_0(X0) )
      & ( ! [X2] :
            ( r1_yellow_0(X0,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X2,X0)
            | v1_xboole_0(X2) )
        | v24_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r1_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        | ~ v24_waybel_0(X0) )
      & ( ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
        | v24_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r1_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        | ~ v24_waybel_0(X0) )
      & ( ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
        | v24_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ( v24_waybel_0(X0)
      <~> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ( v24_waybel_0(X0)
      <~> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',t75_waybel_0)).

fof(f285,plain,
    ( ~ spl15_35
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f278,f194,f283])).

fof(f278,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f90,f195])).

fof(f90,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ v24_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f277,plain,
    ( spl15_32
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f270,f194,f275])).

fof(f270,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f88,f195])).

fof(f88,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ v24_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f268,plain,
    ( spl15_30
    | spl15_15 ),
    inference(avatar_split_clause,[],[f261,f197,f266])).

fof(f261,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X2,sK0)
        | v1_xboole_0(X2) )
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f86,f198])).

fof(f86,plain,(
    ! [X2] :
      ( r1_yellow_0(sK0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_waybel_0(X2,sK0)
      | v1_xboole_0(X2)
      | v24_waybel_0(sK0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f234,plain,
    ( spl15_22
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f230,f176,f232])).

fof(f176,plain,
    ( spl15_8
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | sP14(X0) )
    | ~ spl15_8 ),
    inference(resolution,[],[f142,f177])).

fof(f177,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f218,plain,
    ( spl15_20
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f207,f176,f216])).

fof(f207,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl15_8 ),
    inference(backward_demodulation,[],[f206,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',t6_boole)).

fof(f206,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl15_8 ),
    inference(resolution,[],[f92,f177])).

fof(f205,plain,
    ( ~ spl15_15
    | ~ spl15_17 ),
    inference(avatar_split_clause,[],[f87,f203,f197])).

fof(f87,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v24_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f178,plain,(
    spl15_8 ),
    inference(avatar_split_clause,[],[f91,f176])).

fof(f91,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t75_waybel_0.p',dt_o_0_0_xboole_0)).

fof(f171,plain,(
    spl15_6 ),
    inference(avatar_split_clause,[],[f85,f169])).

fof(f85,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f164,plain,(
    spl15_4 ),
    inference(avatar_split_clause,[],[f84,f162])).

fof(f84,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f157,plain,(
    spl15_2 ),
    inference(avatar_split_clause,[],[f83,f155])).

fof(f83,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f150,plain,(
    ~ spl15_1 ),
    inference(avatar_split_clause,[],[f82,f148])).

fof(f82,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
