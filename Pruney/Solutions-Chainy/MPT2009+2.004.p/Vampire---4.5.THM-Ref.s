%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 257 expanded)
%              Number of leaves         :   25 (  90 expanded)
%              Depth                    :   14
%              Number of atoms          :  380 ( 900 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f113,f119,f141,f151,f160,f169,f182,f226,f245,f268,f277,f294,f296,f302,f307])).

fof(f307,plain,
    ( spl5_21
    | spl5_13
    | ~ spl5_6
    | ~ spl5_10
    | spl5_11
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f303,f266,f103,f136,f106,f85,f180,f292])).

fof(f292,plain,
    ( spl5_21
  <=> r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f180,plain,
    ( spl5_13
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f85,plain,
    ( spl5_6
  <=> m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f106,plain,
    ( spl5_10
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f136,plain,
    ( spl5_11
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f103,plain,
    ( spl5_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f266,plain,
    ( spl5_18
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f303,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ spl5_18 ),
    inference(resolution,[],[f267,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f267,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f266])).

fof(f302,plain,(
    ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | ~ spl5_21 ),
    inference(resolution,[],[f293,f29])).

fof(f29,plain,(
    ~ r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

fof(f293,plain,
    ( r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f292])).

fof(f296,plain,(
    ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl5_13 ),
    inference(resolution,[],[f181,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f181,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f180])).

fof(f294,plain,
    ( spl5_21
    | spl5_13
    | ~ spl5_6
    | ~ spl5_10
    | spl5_11
    | ~ spl5_9
    | spl5_17 ),
    inference(avatar_split_clause,[],[f289,f263,f103,f136,f106,f85,f180,f292])).

fof(f263,plain,
    ( spl5_17
  <=> m1_subset_1(sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f289,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | spl5_17 ),
    inference(resolution,[],[f264,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f264,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1))),u1_struct_0(sK1))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f263])).

fof(f277,plain,(
    ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl5_11 ),
    inference(resolution,[],[f137,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f137,plain,
    ( v2_struct_0(sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f268,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_17
    | spl5_7
    | spl5_18
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f261,f224,f266,f88,f263,f82,f79,f76,f66])).

fof(f66,plain,
    ( spl5_1
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f76,plain,
    ( spl5_3
  <=> m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f79,plain,
    ( spl5_4
  <=> v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f82,plain,
    ( spl5_5
  <=> v1_funct_1(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f88,plain,
    ( spl5_7
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f224,plain,
    ( spl5_16
  <=> k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f261,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_16 ),
    inference(superposition,[],[f32,f225])).

fof(f225,plain,
    ( k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1))))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f224])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

fof(f245,plain,
    ( spl5_11
    | ~ spl5_12
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f244,f66,f139,f136])).

fof(f139,plain,
    ( spl5_12
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f244,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f67,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f67,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f226,plain,
    ( spl5_1
    | spl5_16 ),
    inference(avatar_split_clause,[],[f221,f224,f66])).

fof(f221,plain,
    ( k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f211,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f211,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) ),
    inference(resolution,[],[f148,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) ),
    inference(global_subsumption,[],[f30,f31,f28,f143])).

fof(f143,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK0)
      | k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) ) ),
    inference(resolution,[],[f62,f29])).

fof(f62,plain,(
    ! [X4,X5,X3] :
      ( r1_waybel_0(X3,sK1,X4)
      | ~ l1_struct_0(X3)
      | ~ l1_waybel_0(sK1,X3)
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v2_struct_0(X3)
      | k2_waybel_0(sK0,sK1,sK3(X3,sK1,X4,X5)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(X3,sK1,X4,X5)) ) ),
    inference(global_subsumption,[],[f27,f60])).

fof(f60,plain,(
    ! [X4,X5,X3] :
      ( k2_waybel_0(sK0,sK1,sK3(X3,sK1,X4,X5)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(X3,sK1,X4,X5))
      | ~ l1_struct_0(X3)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,X3)
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v2_struct_0(X3)
      | r1_waybel_0(X3,sK1,X4) ) ),
    inference(resolution,[],[f57,f37])).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k2_waybel_0(sK0,sK1,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0) ) ),
    inference(global_subsumption,[],[f27,f30,f31,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | k2_waybel_0(sK0,sK1,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0) ) ),
    inference(resolution,[],[f36,f28])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).

fof(f28,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f182,plain,
    ( spl5_13
    | ~ spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f178,f88,f103,f180])).

fof(f178,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f89,f35])).

fof(f89,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f169,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | spl5_3 ),
    inference(avatar_split_clause,[],[f167,f76,f106,f103])).

fof(f167,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | spl5_3 ),
    inference(resolution,[],[f77,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f77,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f160,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | spl5_4 ),
    inference(avatar_split_clause,[],[f159,f79,f106,f103])).

fof(f159,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | spl5_4 ),
    inference(resolution,[],[f80,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,
    ( ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f151,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl5_12 ),
    inference(resolution,[],[f142,f50])).

fof(f50,plain,(
    l1_orders_2(sK1) ),
    inference(global_subsumption,[],[f31,f49])).

fof(f49,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1) ),
    inference(resolution,[],[f34,f28])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f142,plain,
    ( ~ l1_orders_2(sK1)
    | spl5_12 ),
    inference(resolution,[],[f140,f33])).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f140,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,
    ( spl5_11
    | ~ spl5_12
    | spl5_6 ),
    inference(avatar_split_clause,[],[f134,f85,f139,f136])).

fof(f134,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | spl5_6 ),
    inference(resolution,[],[f130,f35])).

fof(f130,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | spl5_6 ),
    inference(resolution,[],[f124,f42])).

fof(f124,plain,
    ( ~ r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl5_6 ),
    inference(resolution,[],[f86,f44])).

fof(f86,plain,
    ( ~ m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f119,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl5_10 ),
    inference(resolution,[],[f107,f28])).

fof(f107,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f113,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl5_9 ),
    inference(resolution,[],[f104,f31])).

fof(f104,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f108,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | spl5_5 ),
    inference(avatar_split_clause,[],[f101,f82,f106,f103])).

fof(f101,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | spl5_5 ),
    inference(resolution,[],[f83,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,
    ( ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (25037)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.47  % (25045)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.49  % (25037)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (25045)Refutation not found, incomplete strategy% (25045)------------------------------
% 0.22/0.49  % (25045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25045)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25045)Memory used [KB]: 6140
% 0.22/0.49  % (25045)Time elapsed: 0.073 s
% 0.22/0.49  % (25045)------------------------------
% 0.22/0.49  % (25045)------------------------------
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f309,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f108,f113,f119,f141,f151,f160,f169,f182,f226,f245,f268,f277,f294,f296,f302,f307])).
% 0.22/0.49  fof(f307,plain,(
% 0.22/0.49    spl5_21 | spl5_13 | ~spl5_6 | ~spl5_10 | spl5_11 | ~spl5_9 | ~spl5_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f303,f266,f103,f136,f106,f85,f180,f292])).
% 0.22/0.49  fof(f292,plain,(
% 0.22/0.49    spl5_21 <=> r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    spl5_13 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl5_6 <=> m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    spl5_10 <=> l1_waybel_0(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    spl5_11 <=> v2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    spl5_9 <=> l1_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.49  fof(f266,plain,(
% 0.22/0.49    spl5_18 <=> r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.49  fof(f303,plain,(
% 0.22/0.49    ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~spl5_18),
% 0.22/0.49    inference(resolution,[],[f267,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X0) | r1_waybel_0(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).
% 0.22/0.49  fof(f267,plain,(
% 0.22/0.49    r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~spl5_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f266])).
% 0.22/0.49  fof(f302,plain,(
% 0.22/0.49    ~spl5_21),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f297])).
% 0.22/0.49  fof(f297,plain,(
% 0.22/0.49    $false | ~spl5_21),
% 0.22/0.49    inference(resolution,[],[f293,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ~r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).
% 0.22/0.49  fof(f293,plain,(
% 0.22/0.49    r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | ~spl5_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f292])).
% 0.22/0.49  fof(f296,plain,(
% 0.22/0.49    ~spl5_13),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f295])).
% 0.22/0.49  fof(f295,plain,(
% 0.22/0.49    $false | ~spl5_13),
% 0.22/0.49    inference(resolution,[],[f181,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~spl5_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f180])).
% 0.22/0.49  fof(f294,plain,(
% 0.22/0.49    spl5_21 | spl5_13 | ~spl5_6 | ~spl5_10 | spl5_11 | ~spl5_9 | spl5_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f289,f263,f103,f136,f106,f85,f180,f292])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    spl5_17 <=> m1_subset_1(sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1))),u1_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.49  fof(f289,plain,(
% 0.22/0.49    ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | spl5_17),
% 0.22/0.49    inference(resolution,[],[f264,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X0) | r1_waybel_0(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f264,plain,(
% 0.22/0.49    ~m1_subset_1(sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1))),u1_struct_0(sK1)) | spl5_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f263])).
% 0.22/0.49  fof(f277,plain,(
% 0.22/0.49    ~spl5_11),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f276])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    $false | ~spl5_11),
% 0.22/0.49    inference(resolution,[],[f137,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    v2_struct_0(sK1) | ~spl5_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f136])).
% 0.22/0.49  fof(f268,plain,(
% 0.22/0.49    spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_17 | spl5_7 | spl5_18 | ~spl5_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f261,f224,f266,f88,f263,f82,f79,f76,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl5_1 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl5_3 <=> m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl5_4 <=> v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl5_5 <=> v1_funct_1(u1_waybel_0(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl5_7 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    spl5_16 <=> k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.49  fof(f261,plain,(
% 0.22/0.49    r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1))),u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~spl5_16),
% 0.22/0.49    inference(superposition,[],[f32,f225])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))) | ~spl5_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f224])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | v1_xboole_0(X1) | ~m1_subset_1(X2,X0) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    spl5_11 | ~spl5_12 | ~spl5_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f244,f66,f139,f136])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    spl5_12 <=> l1_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.49  fof(f244,plain,(
% 0.22/0.49    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_1),
% 0.22/0.49    inference(resolution,[],[f67,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    v1_xboole_0(u1_struct_0(sK1)) | ~spl5_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f66])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    spl5_1 | spl5_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f221,f224,f66])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),sK4(u1_struct_0(sK1)))) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.49    inference(resolution,[],[f211,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))) )),
% 0.22/0.49    inference(resolution,[],[f148,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))) )),
% 0.22/0.49    inference(global_subsumption,[],[f30,f31,f28,f143])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK0) | k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),X0))) )),
% 0.22/0.49    inference(resolution,[],[f62,f29])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (r1_waybel_0(X3,sK1,X4) | ~l1_struct_0(X3) | ~l1_waybel_0(sK1,X3) | ~m1_subset_1(X5,u1_struct_0(sK1)) | v2_struct_0(X3) | k2_waybel_0(sK0,sK1,sK3(X3,sK1,X4,X5)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(X3,sK1,X4,X5))) )),
% 0.22/0.49    inference(global_subsumption,[],[f27,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (k2_waybel_0(sK0,sK1,sK3(X3,sK1,X4,X5)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK3(X3,sK1,X4,X5)) | ~l1_struct_0(X3) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,X3) | ~m1_subset_1(X5,u1_struct_0(sK1)) | v2_struct_0(X3) | r1_waybel_0(X3,sK1,X4)) )),
% 0.22/0.49    inference(resolution,[],[f57,f37])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k2_waybel_0(sK0,sK1,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0)) )),
% 0.22/0.49    inference(global_subsumption,[],[f27,f30,f31,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | k2_waybel_0(sK0,sK1,X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0)) )),
% 0.22/0.49    inference(resolution,[],[f36,f28])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    l1_waybel_0(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    l1_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    spl5_13 | ~spl5_9 | ~spl5_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f178,f88,f103,f180])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_7),
% 0.22/0.49    inference(resolution,[],[f89,f35])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f88])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    ~spl5_9 | ~spl5_10 | spl5_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f167,f76,f106,f103])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | spl5_3),
% 0.22/0.49    inference(resolution,[],[f77,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl5_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f76])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    ~spl5_9 | ~spl5_10 | spl5_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f159,f79,f106,f103])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | spl5_4),
% 0.22/0.49    inference(resolution,[],[f80,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | spl5_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f79])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    spl5_12),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f150])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    $false | spl5_12),
% 0.22/0.49    inference(resolution,[],[f142,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    l1_orders_2(sK1)),
% 0.22/0.49    inference(global_subsumption,[],[f31,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ~l1_struct_0(sK0) | l1_orders_2(sK1)),
% 0.22/0.49    inference(resolution,[],[f34,f28])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_orders_2(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    ~l1_orders_2(sK1) | spl5_12),
% 0.22/0.49    inference(resolution,[],[f140,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ~l1_struct_0(sK1) | spl5_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f139])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    spl5_11 | ~spl5_12 | spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f134,f85,f139,f136])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    ~l1_struct_0(sK1) | v2_struct_0(sK1) | spl5_6),
% 0.22/0.49    inference(resolution,[],[f130,f35])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    v1_xboole_0(u1_struct_0(sK1)) | spl5_6),
% 0.22/0.49    inference(resolution,[],[f124,f42])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ~r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) | spl5_6),
% 0.22/0.49    inference(resolution,[],[f86,f44])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ~m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) | spl5_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    spl5_10),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f118])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    $false | spl5_10),
% 0.22/0.49    inference(resolution,[],[f107,f28])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    ~l1_waybel_0(sK1,sK0) | spl5_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f106])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    spl5_9),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f111])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    $false | spl5_9),
% 0.22/0.49    inference(resolution,[],[f104,f31])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ~l1_struct_0(sK0) | spl5_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f103])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ~spl5_9 | ~spl5_10 | spl5_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f101,f82,f106,f103])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | spl5_5),
% 0.22/0.49    inference(resolution,[],[f83,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_1(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ~v1_funct_1(u1_waybel_0(sK0,sK1)) | spl5_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f82])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (25037)------------------------------
% 0.22/0.49  % (25037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25037)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (25037)Memory used [KB]: 11001
% 0.22/0.49  % (25037)Time elapsed: 0.069 s
% 0.22/0.49  % (25037)------------------------------
% 0.22/0.49  % (25037)------------------------------
% 0.22/0.50  % (25024)Success in time 0.135 s
%------------------------------------------------------------------------------
