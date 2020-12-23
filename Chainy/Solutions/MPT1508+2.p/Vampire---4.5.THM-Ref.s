%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1508+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:22 EST 2020

% Result     : Theorem 6.52s
% Output     : Refutation 6.52s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 291 expanded)
%              Number of leaves         :   25 ( 140 expanded)
%              Depth                    :   10
%              Number of atoms          :  537 (1501 expanded)
%              Number of equality atoms :   28 ( 135 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5854,f5859,f5864,f5869,f5874,f5879,f5884,f5889,f6023,f6028,f6038,f6810,f6815,f6820,f9423,f12245])).

fof(f12245,plain,
    ( ~ spl280_4
    | ~ spl280_5
    | spl280_8
    | ~ spl280_12
    | ~ spl280_13
    | ~ spl280_15
    | spl280_108
    | ~ spl280_110
    | ~ spl280_378 ),
    inference(avatar_contradiction_clause,[],[f12244])).

fof(f12244,plain,
    ( $false
    | ~ spl280_4
    | ~ spl280_5
    | spl280_8
    | ~ spl280_12
    | ~ spl280_13
    | ~ spl280_15
    | spl280_108
    | ~ spl280_110
    | ~ spl280_378 ),
    inference(subsumption_resolution,[],[f12211,f6037])).

fof(f6037,plain,
    ( v6_lattices(sK0)
    | ~ spl280_15 ),
    inference(avatar_component_clause,[],[f6035])).

fof(f6035,plain,
    ( spl280_15
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_15])])).

fof(f12211,plain,
    ( ~ v6_lattices(sK0)
    | ~ spl280_4
    | ~ spl280_5
    | spl280_8
    | ~ spl280_12
    | ~ spl280_13
    | spl280_108
    | ~ spl280_110
    | ~ spl280_378 ),
    inference(unit_resulting_resolution,[],[f5888,f6027,f6022,f5873,f5868,f6809,f6819,f9422,f4343])).

fof(f4343,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3786])).

fof(f3786,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2988])).

fof(f2988,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2987])).

fof(f2987,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2057])).

fof(f2057,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f9422,plain,
    ( r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | ~ spl280_378 ),
    inference(avatar_component_clause,[],[f9420])).

fof(f9420,plain,
    ( spl280_378
  <=> r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_378])])).

fof(f6819,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl280_110 ),
    inference(avatar_component_clause,[],[f6817])).

fof(f6817,plain,
    ( spl280_110
  <=> m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_110])])).

fof(f6809,plain,
    ( ~ r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | spl280_108 ),
    inference(avatar_component_clause,[],[f6807])).

fof(f6807,plain,
    ( spl280_108
  <=> r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_108])])).

fof(f5868,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl280_4 ),
    inference(avatar_component_clause,[],[f5866])).

fof(f5866,plain,
    ( spl280_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_4])])).

fof(f5873,plain,
    ( l3_lattices(sK0)
    | ~ spl280_5 ),
    inference(avatar_component_clause,[],[f5871])).

fof(f5871,plain,
    ( spl280_5
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_5])])).

fof(f6022,plain,
    ( v9_lattices(sK0)
    | ~ spl280_12 ),
    inference(avatar_component_clause,[],[f6020])).

fof(f6020,plain,
    ( spl280_12
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_12])])).

fof(f6027,plain,
    ( v8_lattices(sK0)
    | ~ spl280_13 ),
    inference(avatar_component_clause,[],[f6025])).

fof(f6025,plain,
    ( spl280_13
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_13])])).

fof(f5888,plain,
    ( ~ v2_struct_0(sK0)
    | spl280_8 ),
    inference(avatar_component_clause,[],[f5886])).

fof(f5886,plain,
    ( spl280_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_8])])).

fof(f9423,plain,
    ( spl280_378
    | ~ spl280_3
    | ~ spl280_4
    | ~ spl280_5
    | spl280_8
    | ~ spl280_109
    | ~ spl280_110 ),
    inference(avatar_split_clause,[],[f9251,f6817,f6812,f5886,f5871,f5866,f5861,f9420])).

fof(f5861,plain,
    ( spl280_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_3])])).

fof(f6812,plain,
    ( spl280_109
  <=> r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_109])])).

fof(f9251,plain,
    ( r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | ~ spl280_3
    | ~ spl280_4
    | ~ spl280_5
    | spl280_8
    | ~ spl280_109
    | ~ spl280_110 ),
    inference(unit_resulting_resolution,[],[f5888,f5873,f5863,f5868,f6814,f6819,f4196])).

fof(f4196,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X4) ) ),
    inference(cnf_transformation,[],[f3748])).

fof(f3748,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK4(X0,X1,X2))
                  & r2_hidden(sK4(X0,X1,X2),X2)
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3746,f3747])).

fof(f3747,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3746,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3745])).

fof(f3745,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2955])).

fof(f2955,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2954])).

fof(f2954,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2815])).

fof(f2815,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(f6814,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2)
    | ~ spl280_109 ),
    inference(avatar_component_clause,[],[f6812])).

fof(f5863,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl280_3 ),
    inference(avatar_component_clause,[],[f5861])).

fof(f6820,plain,
    ( spl280_110
    | spl280_1
    | ~ spl280_2
    | ~ spl280_4
    | ~ spl280_5
    | ~ spl280_6
    | ~ spl280_7
    | spl280_8 ),
    inference(avatar_split_clause,[],[f6735,f5886,f5881,f5876,f5871,f5866,f5856,f5851,f6817])).

fof(f5851,plain,
    ( spl280_1
  <=> sK1 = k16_lattice3(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_1])])).

% (5819)Termination reason: Time limit
% (5819)Termination phase: Saturation

% (5819)Memory used [KB]: 18805
% (5819)Time elapsed: 0.800 s
% (5819)------------------------------
% (5819)------------------------------
fof(f5856,plain,
    ( spl280_2
  <=> r3_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_2])])).

fof(f5876,plain,
    ( spl280_6
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_6])])).

fof(f5881,plain,
    ( spl280_7
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_7])])).

fof(f6735,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl280_1
    | ~ spl280_2
    | ~ spl280_4
    | ~ spl280_5
    | ~ spl280_6
    | ~ spl280_7
    | spl280_8 ),
    inference(unit_resulting_resolution,[],[f5888,f5883,f5878,f5873,f5868,f5858,f5853,f4190])).

fof(f4190,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k16_lattice3(X0,X2) = X1
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3744])).

fof(f3744,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3742,f3743])).

fof(f3743,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3742,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3741])).

fof(f3741,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3740])).

fof(f3740,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2949])).

fof(f2949,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2948])).

fof(f2948,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2915])).

fof(f2915,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(f5853,plain,
    ( sK1 != k16_lattice3(sK0,sK2)
    | spl280_1 ),
    inference(avatar_component_clause,[],[f5851])).

fof(f5858,plain,
    ( r3_lattice3(sK0,sK1,sK2)
    | ~ spl280_2 ),
    inference(avatar_component_clause,[],[f5856])).

fof(f5878,plain,
    ( v4_lattice3(sK0)
    | ~ spl280_6 ),
    inference(avatar_component_clause,[],[f5876])).

fof(f5883,plain,
    ( v10_lattices(sK0)
    | ~ spl280_7 ),
    inference(avatar_component_clause,[],[f5881])).

fof(f6815,plain,
    ( spl280_109
    | spl280_1
    | ~ spl280_2
    | ~ spl280_4
    | ~ spl280_5
    | ~ spl280_6
    | ~ spl280_7
    | spl280_8 ),
    inference(avatar_split_clause,[],[f6736,f5886,f5881,f5876,f5871,f5866,f5856,f5851,f6812])).

fof(f6736,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2)
    | spl280_1
    | ~ spl280_2
    | ~ spl280_4
    | ~ spl280_5
    | ~ spl280_6
    | ~ spl280_7
    | spl280_8 ),
    inference(unit_resulting_resolution,[],[f5888,f5883,f5878,f5873,f5868,f5858,f5853,f4191])).

fof(f4191,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | r3_lattice3(X0,sK3(X0,X1,X2),X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | k16_lattice3(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f3744])).

fof(f6810,plain,
    ( ~ spl280_108
    | spl280_1
    | ~ spl280_2
    | ~ spl280_4
    | ~ spl280_5
    | ~ spl280_6
    | ~ spl280_7
    | spl280_8 ),
    inference(avatar_split_clause,[],[f6737,f5886,f5881,f5876,f5871,f5866,f5856,f5851,f6807])).

fof(f6737,plain,
    ( ~ r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | spl280_1
    | ~ spl280_2
    | ~ spl280_4
    | ~ spl280_5
    | ~ spl280_6
    | ~ spl280_7
    | spl280_8 ),
    inference(unit_resulting_resolution,[],[f5888,f5883,f5878,f5873,f5868,f5858,f5853,f4192])).

fof(f4192,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | k16_lattice3(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f3744])).

fof(f6038,plain,
    ( spl280_15
    | ~ spl280_5
    | ~ spl280_7
    | spl280_8 ),
    inference(avatar_split_clause,[],[f5910,f5886,f5881,f5871,f6035])).

fof(f5910,plain,
    ( v6_lattices(sK0)
    | ~ spl280_5
    | ~ spl280_7
    | spl280_8 ),
    inference(unit_resulting_resolution,[],[f5873,f5883,f5888,f4536])).

fof(f4536,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f3075])).

fof(f3075,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f3074])).

fof(f3074,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2010])).

fof(f2010,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f6028,plain,
    ( spl280_13
    | ~ spl280_5
    | ~ spl280_7
    | spl280_8 ),
    inference(avatar_split_clause,[],[f5912,f5886,f5881,f5871,f6025])).

fof(f5912,plain,
    ( v8_lattices(sK0)
    | ~ spl280_5
    | ~ spl280_7
    | spl280_8 ),
    inference(unit_resulting_resolution,[],[f5873,f5883,f5888,f4538])).

fof(f4538,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f3075])).

fof(f6023,plain,
    ( spl280_12
    | ~ spl280_5
    | ~ spl280_7
    | spl280_8 ),
    inference(avatar_split_clause,[],[f5913,f5886,f5881,f5871,f6020])).

fof(f5913,plain,
    ( v9_lattices(sK0)
    | ~ spl280_5
    | ~ spl280_7
    | spl280_8 ),
    inference(unit_resulting_resolution,[],[f5873,f5883,f5888,f4539])).

fof(f4539,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f3075])).

fof(f5889,plain,(
    ~ spl280_8 ),
    inference(avatar_split_clause,[],[f4179,f5886])).

fof(f4179,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3739])).

fof(f3739,plain,
    ( sK1 != k16_lattice3(sK0,sK2)
    & r3_lattice3(sK0,sK1,sK2)
    & r2_hidden(sK1,sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2945,f3738,f3737,f3736])).

fof(f3736,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k16_lattice3(X0,X2) != X1
                & r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(sK0,X2) != X1
              & r3_lattice3(sK0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3737,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k16_lattice3(sK0,X2) != X1
            & r3_lattice3(sK0,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k16_lattice3(sK0,X2) != sK1
          & r3_lattice3(sK0,sK1,X2)
          & r2_hidden(sK1,X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3738,plain,
    ( ? [X2] :
        ( k16_lattice3(sK0,X2) != sK1
        & r3_lattice3(sK0,sK1,X2)
        & r2_hidden(sK1,X2) )
   => ( sK1 != k16_lattice3(sK0,sK2)
      & r3_lattice3(sK0,sK1,sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2945,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2944])).

fof(f2944,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2924])).

fof(f2924,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f2923])).

fof(f2923,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

fof(f5884,plain,(
    spl280_7 ),
    inference(avatar_split_clause,[],[f4180,f5881])).

fof(f4180,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f3739])).

fof(f5879,plain,(
    spl280_6 ),
    inference(avatar_split_clause,[],[f4181,f5876])).

fof(f4181,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f3739])).

fof(f5874,plain,(
    spl280_5 ),
    inference(avatar_split_clause,[],[f4182,f5871])).

fof(f4182,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f3739])).

fof(f5869,plain,(
    spl280_4 ),
    inference(avatar_split_clause,[],[f4183,f5866])).

fof(f4183,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3739])).

fof(f5864,plain,(
    spl280_3 ),
    inference(avatar_split_clause,[],[f4184,f5861])).

fof(f4184,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f3739])).

fof(f5859,plain,(
    spl280_2 ),
    inference(avatar_split_clause,[],[f4185,f5856])).

fof(f4185,plain,(
    r3_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3739])).

fof(f5854,plain,(
    ~ spl280_1 ),
    inference(avatar_split_clause,[],[f4186,f5851])).

fof(f4186,plain,(
    sK1 != k16_lattice3(sK0,sK2) ),
    inference(cnf_transformation,[],[f3739])).
%------------------------------------------------------------------------------
