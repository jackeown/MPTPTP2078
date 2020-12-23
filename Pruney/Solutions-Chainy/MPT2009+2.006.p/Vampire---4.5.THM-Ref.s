%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 294 expanded)
%              Number of leaves         :   27 ( 100 expanded)
%              Depth                    :   14
%              Number of atoms          :  419 (1033 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f138,f145,f149,f157,f171,f185,f187,f195,f210,f219,f227,f238,f264,f280,f306,f326,f343])).

fof(f343,plain,
    ( spl5_13
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f342,f104,f69,f152])).

fof(f152,plain,
    ( spl5_13
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f69,plain,
    ( spl5_1
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f104,plain,
    ( spl5_4
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f342,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f105,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f105,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f326,plain,(
    ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl5_21 ),
    inference(resolution,[],[f237,f32])).

fof(f32,plain,(
    ~ r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

fof(f237,plain,
    ( r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl5_21
  <=> r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f306,plain,
    ( spl5_21
    | spl5_16
    | ~ spl5_8
    | ~ spl5_12
    | spl5_13
    | ~ spl5_11
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f305,f225,f133,f152,f136,f116,f193,f236])).

fof(f193,plain,
    ( spl5_16
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f116,plain,
    ( spl5_8
  <=> m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f136,plain,
    ( spl5_12
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f133,plain,
    ( spl5_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f225,plain,
    ( spl5_20
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f305,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ spl5_20 ),
    inference(resolution,[],[f226,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f226,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f225])).

fof(f280,plain,(
    ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl5_16 ),
    inference(resolution,[],[f194,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f194,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f193])).

fof(f264,plain,(
    ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl5_13 ),
    inference(resolution,[],[f153,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f153,plain,
    ( v2_struct_0(sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f238,plain,
    ( spl5_21
    | spl5_16
    | ~ spl5_8
    | ~ spl5_12
    | spl5_13
    | ~ spl5_11
    | spl5_19 ),
    inference(avatar_split_clause,[],[f234,f222,f133,f152,f136,f116,f193,f236])).

fof(f222,plain,
    ( spl5_19
  <=> m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f234,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | spl5_19 ),
    inference(resolution,[],[f223,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f223,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f222])).

fof(f227,plain,
    ( spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_19
    | spl5_9
    | spl5_20
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f220,f217,f225,f119,f222,f113,f110,f107,f104])).

fof(f107,plain,
    ( spl5_5
  <=> m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f110,plain,
    ( spl5_6
  <=> v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f113,plain,
    ( spl5_7
  <=> v1_funct_1(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f119,plain,
    ( spl5_9
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f217,plain,
    ( spl5_18
  <=> k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f220,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_18 ),
    inference(superposition,[],[f35,f218])).

fof(f218,plain,
    ( k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f217])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

fof(f219,plain,
    ( ~ spl5_1
    | spl5_18
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f215,f208,f217,f69])).

fof(f208,plain,
    ( spl5_17
  <=> ! [X0] :
        ( k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0)))
        | ~ l1_waybel_0(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f215,plain,
    ( k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ spl5_17 ),
    inference(resolution,[],[f209,f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v6_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_waybel_0)).

fof(f209,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK1)
        | k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f208])).

fof(f210,plain,
    ( ~ spl5_1
    | spl5_17 ),
    inference(avatar_split_clause,[],[f206,f208,f69])).

fof(f206,plain,(
    ! [X0] :
      ( k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0)))
      | ~ l1_struct_0(sK1)
      | ~ l1_waybel_0(X0,sK1) ) ),
    inference(global_subsumption,[],[f30,f203])).

fof(f203,plain,(
    ! [X0] :
      ( k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0)))
      | ~ l1_struct_0(sK1)
      | ~ l1_waybel_0(X0,sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f168,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) ),
    inference(global_subsumption,[],[f33,f34,f31,f163])).

fof(f163,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK0)
      | k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) ),
    inference(resolution,[],[f76,f32])).

fof(f76,plain,(
    ! [X4,X5,X3] :
      ( r1_waybel_0(X3,sK1,X4)
      | ~ l1_struct_0(X3)
      | ~ l1_waybel_0(sK1,X3)
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v2_struct_0(X3)
      | k2_waybel_0(sK0,sK1,sK4(X3,sK1,X4,X5)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(X3,sK1,X4,X5)) ) ),
    inference(global_subsumption,[],[f30,f66])).

fof(f66,plain,(
    ! [X4,X5,X3] :
      ( k2_waybel_0(sK0,sK1,sK4(X3,sK1,X4,X5)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(X3,sK1,X4,X5))
      | ~ l1_struct_0(X3)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,X3)
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v2_struct_0(X3)
      | r1_waybel_0(X3,sK1,X4) ) ),
    inference(resolution,[],[f63,f41])).

fof(f63,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k2_waybel_0(sK0,sK1,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0) ) ),
    inference(global_subsumption,[],[f30,f33,f34,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | k2_waybel_0(sK0,sK1,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0) ) ),
    inference(resolution,[],[f40,f31])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_waybel_0)).

fof(f31,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f195,plain,
    ( spl5_16
    | ~ spl5_11
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f191,f119,f133,f193])).

fof(f191,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(resolution,[],[f120,f39])).

fof(f120,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f187,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | spl5_5 ),
    inference(avatar_split_clause,[],[f186,f107,f136,f133])).

fof(f186,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | spl5_5 ),
    inference(resolution,[],[f108,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f108,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f185,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | spl5_6 ),
    inference(avatar_split_clause,[],[f184,f110,f136,f133])).

fof(f184,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | spl5_6 ),
    inference(resolution,[],[f111,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

% (12133)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
fof(f111,plain,
    ( ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f171,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl5_14 ),
    inference(resolution,[],[f162,f53])).

fof(f53,plain,(
    l1_orders_2(sK1) ),
    inference(global_subsumption,[],[f34,f50])).

fof(f50,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1) ),
    inference(resolution,[],[f37,f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f162,plain,
    ( ~ l1_orders_2(sK1)
    | spl5_14 ),
    inference(resolution,[],[f161,f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

% (12153)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f161,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_14 ),
    inference(resolution,[],[f156,f38])).

fof(f156,plain,
    ( ~ l1_waybel_0(sK2(sK1),sK1)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_14
  <=> l1_waybel_0(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f157,plain,
    ( spl5_13
    | ~ spl5_14
    | ~ spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f150,f116,f69,f155,f152])).

fof(f150,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_waybel_0(sK2(sK1),sK1)
    | v2_struct_0(sK1)
    | spl5_8 ),
    inference(resolution,[],[f117,f46])).

fof(f117,plain,
    ( ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f149,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl5_12 ),
    inference(resolution,[],[f137,f31])).

fof(f137,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f145,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl5_11 ),
    inference(resolution,[],[f134,f34])).

fof(f134,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f138,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | spl5_7 ),
    inference(avatar_split_clause,[],[f131,f113,f136,f133])).

fof(f131,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | spl5_7 ),
    inference(resolution,[],[f114,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f114,plain,
    ( ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f81,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f77,f53])).

fof(f77,plain,
    ( ~ l1_orders_2(sK1)
    | spl5_1 ),
    inference(resolution,[],[f70,f36])).

fof(f70,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:40:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.47  % (12146)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.48  % (12146)Refutation not found, incomplete strategy% (12146)------------------------------
% 0.22/0.48  % (12146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12146)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (12146)Memory used [KB]: 1663
% 0.22/0.48  % (12146)Time elapsed: 0.036 s
% 0.22/0.48  % (12146)------------------------------
% 0.22/0.48  % (12146)------------------------------
% 0.22/0.49  % (12140)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.49  % (12139)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.50  % (12138)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.50  % (12138)Refutation not found, incomplete strategy% (12138)------------------------------
% 0.22/0.50  % (12138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12138)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12138)Memory used [KB]: 10490
% 0.22/0.50  % (12138)Time elapsed: 0.002 s
% 0.22/0.50  % (12138)------------------------------
% 0.22/0.50  % (12138)------------------------------
% 0.22/0.50  % (12129)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (12142)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.50  % (12140)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f344,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f81,f138,f145,f149,f157,f171,f185,f187,f195,f210,f219,f227,f238,f264,f280,f306,f326,f343])).
% 0.22/0.50  fof(f343,plain,(
% 0.22/0.50    spl5_13 | ~spl5_1 | ~spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f342,f104,f69,f152])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    spl5_13 <=> v2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl5_1 <=> l1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl5_4 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.50  fof(f342,plain,(
% 0.22/0.50    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_4),
% 0.22/0.50    inference(resolution,[],[f105,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(sK1)) | ~spl5_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f104])).
% 0.22/0.50  fof(f326,plain,(
% 0.22/0.50    ~spl5_21),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f322])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    $false | ~spl5_21),
% 0.22/0.50    inference(resolution,[],[f237,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ~r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~spl5_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f236])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    spl5_21 <=> r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.50  fof(f306,plain,(
% 0.22/0.50    spl5_21 | spl5_16 | ~spl5_8 | ~spl5_12 | spl5_13 | ~spl5_11 | ~spl5_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f305,f225,f133,f152,f136,f116,f193,f236])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    spl5_16 <=> v2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl5_8 <=> m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl5_12 <=> l1_waybel_0(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl5_11 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    spl5_20 <=> r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~spl5_20),
% 0.22/0.50    inference(resolution,[],[f226,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X0) | r1_waybel_0(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~spl5_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f225])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    ~spl5_16),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f279])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    $false | ~spl5_16),
% 0.22/0.50    inference(resolution,[],[f194,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~spl5_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f193])).
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    ~spl5_13),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f263])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    $false | ~spl5_13),
% 0.22/0.50    inference(resolution,[],[f153,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~v2_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    v2_struct_0(sK1) | ~spl5_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f152])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    spl5_21 | spl5_16 | ~spl5_8 | ~spl5_12 | spl5_13 | ~spl5_11 | spl5_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f234,f222,f133,f152,f136,f116,f193,f236])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    spl5_19 <=> m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | spl5_19),
% 0.22/0.50    inference(resolution,[],[f223,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X0) | r1_waybel_0(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    ~m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1)) | spl5_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f222])).
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_19 | spl5_9 | spl5_20 | ~spl5_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f220,f217,f225,f119,f222,f113,f110,f107,f104])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl5_5 <=> m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl5_6 <=> v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl5_7 <=> v1_funct_1(u1_waybel_0(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl5_9 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    spl5_18 <=> k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~spl5_18),
% 0.22/0.50    inference(superposition,[],[f35,f218])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) | ~spl5_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f217])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | v1_xboole_0(X1) | ~m1_subset_1(X2,X0) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    ~spl5_1 | spl5_18 | ~spl5_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f215,f208,f217,f69])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    spl5_17 <=> ! [X0] : (k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) | ~l1_waybel_0(X0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) | ~l1_struct_0(sK1) | ~spl5_17),
% 0.22/0.50    inference(resolution,[],[f209,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0] : (l1_waybel_0(sK2(X0),X0) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ? [X1] : l1_waybel_0(X1,X0))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v6_waybel_0(X1,X0) & l1_waybel_0(X1,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_waybel_0)).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_waybel_0(X0,sK1) | k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0)))) ) | ~spl5_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f208])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ~spl5_1 | spl5_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f206,f208,f69])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    ( ! [X0] : (k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) | ~l1_struct_0(sK1) | ~l1_waybel_0(X0,sK1)) )),
% 0.22/0.50    inference(global_subsumption,[],[f30,f203])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    ( ! [X0] : (k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,X0))) | ~l1_struct_0(sK1) | ~l1_waybel_0(X0,sK1) | v2_struct_0(sK1)) )),
% 0.22/0.50    inference(resolution,[],[f168,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_yellow_6)).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))) )),
% 0.22/0.50    inference(global_subsumption,[],[f33,f34,f31,f163])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK0) | k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))) )),
% 0.22/0.50    inference(resolution,[],[f76,f32])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (r1_waybel_0(X3,sK1,X4) | ~l1_struct_0(X3) | ~l1_waybel_0(sK1,X3) | ~m1_subset_1(X5,u1_struct_0(sK1)) | v2_struct_0(X3) | k2_waybel_0(sK0,sK1,sK4(X3,sK1,X4,X5)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(X3,sK1,X4,X5))) )),
% 0.22/0.50    inference(global_subsumption,[],[f30,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (k2_waybel_0(sK0,sK1,sK4(X3,sK1,X4,X5)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(X3,sK1,X4,X5)) | ~l1_struct_0(X3) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,X3) | ~m1_subset_1(X5,u1_struct_0(sK1)) | v2_struct_0(X3) | r1_waybel_0(X3,sK1,X4)) )),
% 0.22/0.50    inference(resolution,[],[f63,f41])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k2_waybel_0(sK0,sK1,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0)) )),
% 0.22/0.50    inference(global_subsumption,[],[f30,f33,f34,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | k2_waybel_0(sK0,sK1,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0)) )),
% 0.22/0.50    inference(resolution,[],[f40,f31])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_waybel_0)).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    l1_waybel_0(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    spl5_16 | ~spl5_11 | ~spl5_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f191,f119,f133,f193])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_9),
% 0.22/0.50    inference(resolution,[],[f120,f39])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f119])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ~spl5_11 | ~spl5_12 | spl5_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f186,f107,f136,f133])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | spl5_5),
% 0.22/0.50    inference(resolution,[],[f108,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl5_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f107])).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    ~spl5_11 | ~spl5_12 | spl5_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f184,f110,f136,f133])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | spl5_6),
% 0.22/0.50    inference(resolution,[],[f111,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  % (12133)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | spl5_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f110])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    spl5_14),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    $false | spl5_14),
% 0.22/0.50    inference(resolution,[],[f162,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    l1_orders_2(sK1)),
% 0.22/0.50    inference(global_subsumption,[],[f34,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ~l1_struct_0(sK0) | l1_orders_2(sK1)),
% 0.22/0.50    inference(resolution,[],[f37,f31])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_orders_2(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ~l1_orders_2(sK1) | spl5_14),
% 0.22/0.50    inference(resolution,[],[f161,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  % (12153)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ~l1_struct_0(sK1) | spl5_14),
% 0.22/0.50    inference(resolution,[],[f156,f38])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    ~l1_waybel_0(sK2(sK1),sK1) | spl5_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f155])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    spl5_14 <=> l1_waybel_0(sK2(sK1),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl5_13 | ~spl5_14 | ~spl5_1 | spl5_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f150,f116,f69,f155,f152])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ~l1_struct_0(sK1) | ~l1_waybel_0(sK2(sK1),sK1) | v2_struct_0(sK1) | spl5_8),
% 0.22/0.50    inference(resolution,[],[f117,f46])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | spl5_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f116])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    spl5_12),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f148])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    $false | spl5_12),
% 0.22/0.50    inference(resolution,[],[f137,f31])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ~l1_waybel_0(sK1,sK0) | spl5_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f136])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    spl5_11),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f143])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    $false | spl5_11),
% 0.22/0.50    inference(resolution,[],[f134,f34])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ~l1_struct_0(sK0) | spl5_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ~spl5_11 | ~spl5_12 | spl5_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f131,f113,f136,f133])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | spl5_7),
% 0.22/0.50    inference(resolution,[],[f114,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_funct_1(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ~v1_funct_1(u1_waybel_0(sK0,sK1)) | spl5_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl5_1),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    $false | spl5_1),
% 0.22/0.50    inference(resolution,[],[f77,f53])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ~l1_orders_2(sK1) | spl5_1),
% 0.22/0.50    inference(resolution,[],[f70,f36])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ~l1_struct_0(sK1) | spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f69])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (12140)------------------------------
% 0.22/0.50  % (12140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12140)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (12140)Memory used [KB]: 11001
% 0.22/0.50  % (12140)Time elapsed: 0.090 s
% 0.22/0.50  % (12140)------------------------------
% 0.22/0.50  % (12140)------------------------------
% 0.22/0.51  % (12132)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (12121)Success in time 0.148 s
%------------------------------------------------------------------------------
