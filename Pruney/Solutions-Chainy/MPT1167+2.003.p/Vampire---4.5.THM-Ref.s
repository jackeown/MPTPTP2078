%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:13 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 365 expanded)
%              Number of leaves         :   30 ( 132 expanded)
%              Depth                    :   21
%              Number of atoms          : 1090 (2147 expanded)
%              Number of equality atoms :   57 (  91 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1038,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f90,f95,f100,f141,f146,f151,f161,f166,f182,f232,f254,f324,f381,f444,f715,f751,f960,f1035])).

fof(f1035,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(avatar_contradiction_clause,[],[f1034])).

fof(f1034,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f1033,f89])).

fof(f89,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_6
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1033,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f1031,f99])).

fof(f99,plain,
    ( ~ r2_hidden(sK1,sK4)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_8
  <=> r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1031,plain,
    ( r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK1,sK3)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(resolution,[],[f1014,f140])).

fof(f140,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl6_9
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f1014,plain,
    ( ! [X0] :
        ( ~ r2_orders_2(sK0,X0,sK2)
        | r2_hidden(X0,sK4)
        | ~ r2_hidden(X0,sK3) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f1013,f150])).

fof(f150,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_11
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f1013,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK4)
        | ~ r2_orders_2(sK0,X0,sK2)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f1011,f165])).

fof(f165,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl6_14
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f1011,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X0,sK2)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_51 ),
    inference(resolution,[],[f969,f120])).

fof(f120,plain,
    ( ! [X6,X8,X7] :
        ( r2_hidden(X6,k3_orders_2(sK0,X8,X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X6,X7)
        | ~ r2_hidden(X6,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f119,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f119,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X6,X7)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(X6,k3_orders_2(sK0,X8,X7)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f118,f64])).

fof(f64,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f118,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X6,X7)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(X6,k3_orders_2(sK0,X8,X7)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f117,f79])).

fof(f79,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f117,plain,
    ( ! [X6,X8,X7] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X6,X7)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(X6,k3_orders_2(sK0,X8,X7)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f116,f74])).

fof(f74,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f116,plain,
    ( ! [X6,X8,X7] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X6,X7)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(X6,k3_orders_2(sK0,X8,X7)) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f103,f69])).

fof(f69,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f103,plain,
    ( ! [X6,X8,X7] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X6,X7)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(X6,k3_orders_2(sK0,X8,X7)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f84,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f84,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f969,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_orders_2(sK0,sK3,sK2))
        | r2_hidden(X1,sK4) )
    | ~ spl6_51 ),
    inference(resolution,[],[f959,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f959,plain,
    ( m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(sK4))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f957])).

fof(f957,plain,
    ( spl6_51
  <=> m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f960,plain,
    ( spl6_51
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f950,f423,f225,f163,f158,f92,f82,f77,f72,f67,f62,f957])).

fof(f92,plain,
    ( spl6_7
  <=> r2_hidden(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f158,plain,
    ( spl6_13
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f225,plain,
    ( spl6_17
  <=> sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f423,plain,
    ( spl6_29
  <=> m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f950,plain,
    ( m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(sK4))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(resolution,[],[f926,f94])).

fof(f94,plain,
    ( r2_hidden(sK2,sK4)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f926,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | m1_subset_1(k3_orders_2(sK0,sK3,X0),k1_zfmisc_1(sK4)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f925,f167])).

fof(f167,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK4) )
    | ~ spl6_13 ),
    inference(resolution,[],[f160,f55])).

fof(f160,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f925,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,sK3,X0),k1_zfmisc_1(sK4)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f921,f165])).

fof(f921,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,sK3,X0),k1_zfmisc_1(sK4)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(superposition,[],[f687,f227])).

fof(f227,plain,
    ( sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f225])).

fof(f687,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,sK3,X0),k1_zfmisc_1(sK4)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(resolution,[],[f603,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f603,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_orders_2(sK0,sK3,X0),sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f602,f424])).

fof(f424,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f423])).

fof(f602,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tarski(k3_orders_2(sK0,sK3,X0),sK4)
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(duplicate_literal_removal,[],[f601])).

fof(f601,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tarski(k3_orders_2(sK0,sK3,X0),sK4)
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(resolution,[],[f595,f111])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( r2_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f110,f64])).

fof(f110,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f109,f79])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f108,f74])).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f101,f69])).

fof(f101,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,k3_orders_2(sK0,X2,X1)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f84,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f595,plain,
    ( ! [X3] :
        ( ~ r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_tarski(k3_orders_2(sK0,sK3,X3),sK4) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f399,f424])).

fof(f399,plain,
    ( ! [X3] :
        ( r1_tarski(k3_orders_2(sK0,sK3,X3),sK4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f398,f64])).

fof(f398,plain,
    ( ! [X3] :
        ( r1_tarski(k3_orders_2(sK0,sK3,X3),sK4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f397,f165])).

fof(f397,plain,
    ( ! [X3] :
        ( r1_tarski(k3_orders_2(sK0,sK3,X3),sK4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f396,f84])).

fof(f396,plain,
    ( ! [X3] :
        ( r1_tarski(k3_orders_2(sK0,sK3,X3),sK4)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f395,f79])).

fof(f395,plain,
    ( ! [X3] :
        ( r1_tarski(k3_orders_2(sK0,sK3,X3),sK4)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f394,f74])).

fof(f394,plain,
    ( ! [X3] :
        ( r1_tarski(k3_orders_2(sK0,sK3,X3),sK4)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f388,f69])).

fof(f388,plain,
    ( ! [X3] :
        ( r1_tarski(k3_orders_2(sK0,sK3,X3),sK4)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_17 ),
    inference(superposition,[],[f40,f227])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_orders_2(X0,X1,X2)
                   => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).

fof(f751,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 != sK3
    | r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f715,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_21
    | spl6_23
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f714])).

fof(f714,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_21
    | spl6_23
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f713,f160])).

fof(f713,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_21
    | spl6_23
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f711,f283])).

fof(f283,plain,
    ( k1_xboole_0 != sK4
    | spl6_23 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl6_23
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f711,plain,
    ( k1_xboole_0 = sK4
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(resolution,[],[f493,f253])).

fof(f253,plain,
    ( m1_orders_2(sK4,sK0,k1_xboole_0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl6_21
  <=> m1_orders_2(sK4,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f493,plain,
    ( ! [X1] :
        ( ~ m1_orders_2(X1,sK0,k1_xboole_0)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f492,f64])).

fof(f492,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | ~ m1_orders_2(X1,sK0,k1_xboole_0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f491,f84])).

fof(f491,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | ~ m1_orders_2(X1,sK0,k1_xboole_0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f490,f79])).

fof(f490,plain,
    ( ! [X1] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | ~ m1_orders_2(X1,sK0,k1_xboole_0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f489,f74])).

fof(f489,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | ~ m1_orders_2(X1,sK0,k1_xboole_0) )
    | ~ spl6_2
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f480,f69])).

fof(f480,plain,
    ( ! [X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | ~ m1_orders_2(X1,sK0,k1_xboole_0) )
    | ~ spl6_28 ),
    inference(resolution,[],[f380,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(f380,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl6_28
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f444,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | spl6_18
    | spl6_29 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14
    | spl6_18
    | spl6_29 ),
    inference(subsumption_resolution,[],[f442,f145])).

fof(f145,plain,
    ( m1_orders_2(sK4,sK0,sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_10
  <=> m1_orders_2(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f442,plain,
    ( ~ m1_orders_2(sK4,sK0,sK3)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_14
    | spl6_18
    | spl6_29 ),
    inference(subsumption_resolution,[],[f441,f64])).

fof(f441,plain,
    ( v2_struct_0(sK0)
    | ~ m1_orders_2(sK4,sK0,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_14
    | spl6_18
    | spl6_29 ),
    inference(subsumption_resolution,[],[f440,f230])).

fof(f230,plain,
    ( k1_xboole_0 != sK3
    | spl6_18 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl6_18
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f440,plain,
    ( k1_xboole_0 = sK3
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK4,sK0,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_14
    | spl6_29 ),
    inference(subsumption_resolution,[],[f439,f160])).

fof(f439,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK4,sK0,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | spl6_29 ),
    inference(subsumption_resolution,[],[f438,f165])).

fof(f438,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK4,sK0,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_29 ),
    inference(subsumption_resolution,[],[f437,f84])).

fof(f437,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK4,sK0,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_29 ),
    inference(subsumption_resolution,[],[f436,f79])).

fof(f436,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK4,sK0,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_29 ),
    inference(subsumption_resolution,[],[f435,f74])).

fof(f435,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK4,sK0,sK3)
    | ~ spl6_2
    | spl6_29 ),
    inference(subsumption_resolution,[],[f430,f69])).

fof(f430,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK4,sK0,sK3)
    | spl6_29 ),
    inference(resolution,[],[f425,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | v2_struct_0(X0)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f425,plain,
    ( ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f423])).

fof(f381,plain,
    ( spl6_28
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f376,f321,f378])).

fof(f321,plain,
    ( spl6_26
  <=> r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f376,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_26 ),
    inference(resolution,[],[f323,f52])).

fof(f323,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f321])).

fof(f324,plain,
    ( spl6_26
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f317,f229,f179,f321])).

fof(f179,plain,
    ( spl6_16
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f317,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(superposition,[],[f181,f231])).

fof(f231,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f229])).

fof(f181,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f179])).

fof(f254,plain,
    ( spl6_21
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f234,f229,f143,f251])).

fof(f234,plain,
    ( m1_orders_2(sK4,sK0,k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(superposition,[],[f145,f231])).

fof(f232,plain,
    ( spl6_17
    | spl6_18
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f222,f163,f158,f143,f82,f77,f72,f67,f62,f229,f225])).

fof(f222,plain,
    ( k1_xboole_0 = sK3
    | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f221,f165])).

fof(f221,plain,
    ( k1_xboole_0 = sK3
    | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f220,f160])).

fof(f220,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3
    | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(resolution,[],[f128,f145])).

fof(f128,plain,
    ( ! [X12,X11] :
        ( ~ m1_orders_2(X12,sK0,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X11
        | k3_orders_2(sK0,X11,sK5(sK0,X11,X12)) = X12
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f127,f64])).

fof(f127,plain,
    ( ! [X12,X11] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X11
        | k3_orders_2(sK0,X11,sK5(sK0,X11,X12)) = X12
        | ~ m1_orders_2(X12,sK0,X11) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f126,f79])).

fof(f126,plain,
    ( ! [X12,X11] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X11
        | k3_orders_2(sK0,X11,sK5(sK0,X11,X12)) = X12
        | ~ m1_orders_2(X12,sK0,X11) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f125,f74])).

fof(f125,plain,
    ( ! [X12,X11] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X11
        | k3_orders_2(sK0,X11,sK5(sK0,X11,X12)) = X12
        | ~ m1_orders_2(X12,sK0,X11) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f105,f69])).

fof(f105,plain,
    ( ! [X12,X11] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X11
        | k3_orders_2(sK0,X11,sK5(sK0,X11,X12)) = X12
        | ~ m1_orders_2(X12,sK0,X11) )
    | ~ spl6_5 ),
    inference(resolution,[],[f84,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f182,plain,
    ( spl6_16
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f171,f163,f179])).

fof(f171,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_14 ),
    inference(resolution,[],[f165,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f166,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f32,f163])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,X0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,X0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( ( m1_orders_2(X4,X0,X3)
                            & r2_hidden(X2,X4)
                            & r2_hidden(X1,X3)
                            & r2_orders_2(X0,X1,X2) )
                         => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( ( m1_orders_2(X4,X0,X3)
                          & r2_hidden(X2,X4)
                          & r2_hidden(X1,X3)
                          & r2_orders_2(X0,X1,X2) )
                       => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).

fof(f161,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f26,f158])).

fof(f26,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f151,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f33,f148])).

fof(f33,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f146,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f30,f143])).

fof(f30,plain,(
    m1_orders_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f141,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f27,f138])).

fof(f27,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f100,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f31,f97])).

fof(f31,plain,(
    ~ r2_hidden(sK1,sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f95,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f29,f92])).

fof(f29,plain,(
    r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f90,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f28,f87])).

fof(f28,plain,(
    r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f85,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f38,f77])).

fof(f38,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (3755)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.46  % (3775)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.47  % (3767)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.48  % (3762)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.48  % (3766)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.49  % (3769)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.49  % (3774)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.49  % (3761)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.49  % (3764)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.50  % (3756)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (3757)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.50  % (3768)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.50  % (3758)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (3759)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.50  % (3756)Refutation not found, incomplete strategy% (3756)------------------------------
% 0.19/0.50  % (3756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (3756)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (3756)Memory used [KB]: 10618
% 0.19/0.50  % (3756)Time elapsed: 0.065 s
% 0.19/0.50  % (3756)------------------------------
% 0.19/0.50  % (3756)------------------------------
% 0.19/0.51  % (3772)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.51  % (3760)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  % (3765)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.51  % (3763)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.51  % (3770)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.52  % (3773)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.28/0.53  % (3771)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.47/0.55  % (3758)Refutation found. Thanks to Tanya!
% 1.47/0.55  % SZS status Theorem for theBenchmark
% 1.47/0.55  % SZS output start Proof for theBenchmark
% 1.47/0.55  fof(f1038,plain,(
% 1.47/0.55    $false),
% 1.47/0.55    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f90,f95,f100,f141,f146,f151,f161,f166,f182,f232,f254,f324,f381,f444,f715,f751,f960,f1035])).
% 1.47/0.55  fof(f1035,plain,(
% 1.47/0.55    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_8 | ~spl6_9 | ~spl6_11 | ~spl6_14 | ~spl6_51),
% 1.47/0.55    inference(avatar_contradiction_clause,[],[f1034])).
% 1.47/0.55  fof(f1034,plain,(
% 1.47/0.55    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_8 | ~spl6_9 | ~spl6_11 | ~spl6_14 | ~spl6_51)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1033,f89])).
% 1.47/0.55  fof(f89,plain,(
% 1.47/0.55    r2_hidden(sK1,sK3) | ~spl6_6),
% 1.47/0.55    inference(avatar_component_clause,[],[f87])).
% 1.47/0.55  fof(f87,plain,(
% 1.47/0.55    spl6_6 <=> r2_hidden(sK1,sK3)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.47/0.55  fof(f1033,plain,(
% 1.47/0.55    ~r2_hidden(sK1,sK3) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_8 | ~spl6_9 | ~spl6_11 | ~spl6_14 | ~spl6_51)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1031,f99])).
% 1.47/0.55  fof(f99,plain,(
% 1.47/0.55    ~r2_hidden(sK1,sK4) | spl6_8),
% 1.47/0.55    inference(avatar_component_clause,[],[f97])).
% 1.47/0.55  fof(f97,plain,(
% 1.47/0.55    spl6_8 <=> r2_hidden(sK1,sK4)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.47/0.55  fof(f1031,plain,(
% 1.47/0.55    r2_hidden(sK1,sK4) | ~r2_hidden(sK1,sK3) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_9 | ~spl6_11 | ~spl6_14 | ~spl6_51)),
% 1.47/0.55    inference(resolution,[],[f1014,f140])).
% 1.47/0.55  fof(f140,plain,(
% 1.47/0.55    r2_orders_2(sK0,sK1,sK2) | ~spl6_9),
% 1.47/0.55    inference(avatar_component_clause,[],[f138])).
% 1.47/0.55  fof(f138,plain,(
% 1.47/0.55    spl6_9 <=> r2_orders_2(sK0,sK1,sK2)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.47/0.55  fof(f1014,plain,(
% 1.47/0.55    ( ! [X0] : (~r2_orders_2(sK0,X0,sK2) | r2_hidden(X0,sK4) | ~r2_hidden(X0,sK3)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_14 | ~spl6_51)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1013,f150])).
% 1.47/0.55  fof(f150,plain,(
% 1.47/0.55    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_11),
% 1.47/0.55    inference(avatar_component_clause,[],[f148])).
% 1.47/0.55  fof(f148,plain,(
% 1.47/0.55    spl6_11 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.47/0.55  fof(f1013,plain,(
% 1.47/0.55    ( ! [X0] : (r2_hidden(X0,sK4) | ~r2_orders_2(sK0,X0,sK2) | ~r2_hidden(X0,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_51)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1011,f165])).
% 1.47/0.56  fof(f165,plain,(
% 1.47/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_14),
% 1.47/0.56    inference(avatar_component_clause,[],[f163])).
% 1.47/0.56  fof(f163,plain,(
% 1.47/0.56    spl6_14 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.47/0.56  fof(f1011,plain,(
% 1.47/0.56    ( ! [X0] : (r2_hidden(X0,sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,sK2) | ~r2_hidden(X0,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_51)),
% 1.47/0.56    inference(resolution,[],[f969,f120])).
% 1.47/0.56  fof(f120,plain,(
% 1.47/0.56    ( ! [X6,X8,X7] : (r2_hidden(X6,k3_orders_2(sK0,X8,X7)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X6,X7) | ~r2_hidden(X6,X8) | ~m1_subset_1(X7,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f119,f55])).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f25])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.47/0.56    inference(flattening,[],[f24])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f3])).
% 1.47/0.56  fof(f3,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.47/0.56  fof(f119,plain,(
% 1.47/0.56    ( ! [X6,X8,X7] : (~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X6,X7) | ~r2_hidden(X6,X8) | r2_hidden(X6,k3_orders_2(sK0,X8,X7))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f118,f64])).
% 1.47/0.56  fof(f64,plain,(
% 1.47/0.56    ~v2_struct_0(sK0) | spl6_1),
% 1.47/0.56    inference(avatar_component_clause,[],[f62])).
% 1.47/0.56  fof(f62,plain,(
% 1.47/0.56    spl6_1 <=> v2_struct_0(sK0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.47/0.56  fof(f118,plain,(
% 1.47/0.56    ( ! [X6,X8,X7] : (v2_struct_0(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X6,X7) | ~r2_hidden(X6,X8) | r2_hidden(X6,k3_orders_2(sK0,X8,X7))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f117,f79])).
% 1.47/0.56  fof(f79,plain,(
% 1.47/0.56    v5_orders_2(sK0) | ~spl6_4),
% 1.47/0.56    inference(avatar_component_clause,[],[f77])).
% 1.47/0.56  fof(f77,plain,(
% 1.47/0.56    spl6_4 <=> v5_orders_2(sK0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.47/0.56  fof(f117,plain,(
% 1.47/0.56    ( ! [X6,X8,X7] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X6,X7) | ~r2_hidden(X6,X8) | r2_hidden(X6,k3_orders_2(sK0,X8,X7))) ) | (~spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f116,f74])).
% 1.47/0.56  fof(f74,plain,(
% 1.47/0.56    v4_orders_2(sK0) | ~spl6_3),
% 1.47/0.56    inference(avatar_component_clause,[],[f72])).
% 1.47/0.56  fof(f72,plain,(
% 1.47/0.56    spl6_3 <=> v4_orders_2(sK0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.47/0.56  fof(f116,plain,(
% 1.47/0.56    ( ! [X6,X8,X7] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X6,X7) | ~r2_hidden(X6,X8) | r2_hidden(X6,k3_orders_2(sK0,X8,X7))) ) | (~spl6_2 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f103,f69])).
% 1.47/0.56  fof(f69,plain,(
% 1.47/0.56    v3_orders_2(sK0) | ~spl6_2),
% 1.47/0.56    inference(avatar_component_clause,[],[f67])).
% 1.47/0.56  fof(f67,plain,(
% 1.47/0.56    spl6_2 <=> v3_orders_2(sK0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.47/0.56  fof(f103,plain,(
% 1.47/0.56    ( ! [X6,X8,X7] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X6,X7) | ~r2_hidden(X6,X8) | r2_hidden(X6,k3_orders_2(sK0,X8,X7))) ) | ~spl6_5),
% 1.47/0.56    inference(resolution,[],[f84,f43])).
% 1.47/0.56  fof(f43,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,X3) | r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f16])).
% 1.47/0.56  fof(f16,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.47/0.56    inference(flattening,[],[f15])).
% 1.47/0.56  fof(f15,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f7])).
% 1.47/0.56  fof(f7,axiom,(
% 1.47/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 1.47/0.56  fof(f84,plain,(
% 1.47/0.56    l1_orders_2(sK0) | ~spl6_5),
% 1.47/0.56    inference(avatar_component_clause,[],[f82])).
% 1.47/0.56  fof(f82,plain,(
% 1.47/0.56    spl6_5 <=> l1_orders_2(sK0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.47/0.56  fof(f969,plain,(
% 1.47/0.56    ( ! [X1] : (~r2_hidden(X1,k3_orders_2(sK0,sK3,sK2)) | r2_hidden(X1,sK4)) ) | ~spl6_51),
% 1.47/0.56    inference(resolution,[],[f959,f50])).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f19])).
% 1.47/0.56  fof(f19,plain,(
% 1.47/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.47/0.56  fof(f959,plain,(
% 1.47/0.56    m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(sK4)) | ~spl6_51),
% 1.47/0.56    inference(avatar_component_clause,[],[f957])).
% 1.47/0.56  fof(f957,plain,(
% 1.47/0.56    spl6_51 <=> m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(sK4))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 1.47/0.56  fof(f960,plain,(
% 1.47/0.56    spl6_51 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_29),
% 1.47/0.56    inference(avatar_split_clause,[],[f950,f423,f225,f163,f158,f92,f82,f77,f72,f67,f62,f957])).
% 1.47/0.56  fof(f92,plain,(
% 1.47/0.56    spl6_7 <=> r2_hidden(sK2,sK4)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.47/0.56  fof(f158,plain,(
% 1.47/0.56    spl6_13 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.47/0.56  fof(f225,plain,(
% 1.47/0.56    spl6_17 <=> sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.47/0.56  fof(f423,plain,(
% 1.47/0.56    spl6_29 <=> m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.47/0.56  fof(f950,plain,(
% 1.47/0.56    m1_subset_1(k3_orders_2(sK0,sK3,sK2),k1_zfmisc_1(sK4)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_29)),
% 1.47/0.56    inference(resolution,[],[f926,f94])).
% 1.47/0.56  fof(f94,plain,(
% 1.47/0.56    r2_hidden(sK2,sK4) | ~spl6_7),
% 1.47/0.56    inference(avatar_component_clause,[],[f92])).
% 1.47/0.56  fof(f926,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,sK4) | m1_subset_1(k3_orders_2(sK0,sK3,X0),k1_zfmisc_1(sK4))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_13 | ~spl6_14 | ~spl6_17 | ~spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f925,f167])).
% 1.47/0.56  fof(f167,plain,(
% 1.47/0.56    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK4)) ) | ~spl6_13),
% 1.47/0.56    inference(resolution,[],[f160,f55])).
% 1.47/0.56  fof(f160,plain,(
% 1.47/0.56    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_13),
% 1.47/0.56    inference(avatar_component_clause,[],[f158])).
% 1.47/0.56  fof(f925,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,sK3,X0),k1_zfmisc_1(sK4))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_17 | ~spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f921,f165])).
% 1.47/0.56  fof(f921,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,sK3,X0),k1_zfmisc_1(sK4))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_17 | ~spl6_29)),
% 1.47/0.56    inference(superposition,[],[f687,f227])).
% 1.47/0.56  fof(f227,plain,(
% 1.47/0.56    sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) | ~spl6_17),
% 1.47/0.56    inference(avatar_component_clause,[],[f225])).
% 1.47/0.56  fof(f687,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,sK3,X0),k1_zfmisc_1(sK4))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_17 | ~spl6_29)),
% 1.47/0.56    inference(resolution,[],[f603,f52])).
% 1.47/0.56  fof(f52,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.47/0.56  fof(f603,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k3_orders_2(sK0,sK3,X0),sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_17 | ~spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f602,f424])).
% 1.47/0.56  fof(f424,plain,(
% 1.47/0.56    m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~spl6_29),
% 1.47/0.56    inference(avatar_component_clause,[],[f423])).
% 1.47/0.56  fof(f602,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK3,X0),sK4) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_17 | ~spl6_29)),
% 1.47/0.56    inference(duplicate_literal_removal,[],[f601])).
% 1.47/0.56  fof(f601,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK3,X0),sK4) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,X1,sK5(sK0,sK3,sK4)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_17 | ~spl6_29)),
% 1.47/0.56    inference(resolution,[],[f595,f111])).
% 1.47/0.56  fof(f111,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f110,f64])).
% 1.47/0.56  fof(f110,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f109,f79])).
% 1.47/0.56  fof(f109,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f108,f74])).
% 1.47/0.56  fof(f108,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | (~spl6_2 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f101,f69])).
% 1.47/0.56  fof(f101,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k3_orders_2(sK0,X2,X1))) ) | ~spl6_5),
% 1.47/0.56    inference(resolution,[],[f84,f41])).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f16])).
% 1.47/0.56  fof(f595,plain,(
% 1.47/0.56    ( ! [X3] : (~r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_tarski(k3_orders_2(sK0,sK3,X3),sK4)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_17 | ~spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f399,f424])).
% 1.47/0.56  fof(f399,plain,(
% 1.47/0.56    ( ! [X3] : (r1_tarski(k3_orders_2(sK0,sK3,X3),sK4) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_17)),
% 1.47/0.56    inference(subsumption_resolution,[],[f398,f64])).
% 1.47/0.56  fof(f398,plain,(
% 1.47/0.56    ( ! [X3] : (r1_tarski(k3_orders_2(sK0,sK3,X3),sK4) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_17)),
% 1.47/0.56    inference(subsumption_resolution,[],[f397,f165])).
% 1.47/0.56  fof(f397,plain,(
% 1.47/0.56    ( ! [X3] : (r1_tarski(k3_orders_2(sK0,sK3,X3),sK4) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17)),
% 1.47/0.56    inference(subsumption_resolution,[],[f396,f84])).
% 1.47/0.56  fof(f396,plain,(
% 1.47/0.56    ( ! [X3] : (r1_tarski(k3_orders_2(sK0,sK3,X3),sK4) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_17)),
% 1.47/0.56    inference(subsumption_resolution,[],[f395,f79])).
% 1.47/0.56  fof(f395,plain,(
% 1.47/0.56    ( ! [X3] : (r1_tarski(k3_orders_2(sK0,sK3,X3),sK4) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_17)),
% 1.47/0.56    inference(subsumption_resolution,[],[f394,f74])).
% 1.47/0.56  fof(f394,plain,(
% 1.47/0.56    ( ! [X3] : (r1_tarski(k3_orders_2(sK0,sK3,X3),sK4) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_17)),
% 1.47/0.56    inference(subsumption_resolution,[],[f388,f69])).
% 1.47/0.56  fof(f388,plain,(
% 1.47/0.56    ( ! [X3] : (r1_tarski(k3_orders_2(sK0,sK3,X3),sK4) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X3,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | ~spl6_17),
% 1.47/0.56    inference(superposition,[],[f40,f227])).
% 1.47/0.56  fof(f40,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f14])).
% 1.47/0.56  fof(f14,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.47/0.56    inference(flattening,[],[f13])).
% 1.47/0.56  fof(f13,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) | ~r2_orders_2(X0,X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f8])).
% 1.47/0.56  fof(f8,axiom,(
% 1.47/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_orders_2(X0,X1,X2) => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)))))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).
% 1.47/0.56  fof(f751,plain,(
% 1.47/0.56    k1_xboole_0 != sK4 | k1_xboole_0 != sK3 | r2_hidden(sK1,sK4) | ~r2_hidden(sK1,sK3)),
% 1.47/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.47/0.56  fof(f715,plain,(
% 1.47/0.56    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_13 | ~spl6_21 | spl6_23 | ~spl6_28),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f714])).
% 1.47/0.56  fof(f714,plain,(
% 1.47/0.56    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_13 | ~spl6_21 | spl6_23 | ~spl6_28)),
% 1.47/0.56    inference(subsumption_resolution,[],[f713,f160])).
% 1.47/0.56  fof(f713,plain,(
% 1.47/0.56    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_21 | spl6_23 | ~spl6_28)),
% 1.47/0.56    inference(subsumption_resolution,[],[f711,f283])).
% 1.47/0.56  fof(f283,plain,(
% 1.47/0.56    k1_xboole_0 != sK4 | spl6_23),
% 1.47/0.56    inference(avatar_component_clause,[],[f282])).
% 1.47/0.56  fof(f282,plain,(
% 1.47/0.56    spl6_23 <=> k1_xboole_0 = sK4),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.47/0.56  fof(f711,plain,(
% 1.47/0.56    k1_xboole_0 = sK4 | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_21 | ~spl6_28)),
% 1.47/0.56    inference(resolution,[],[f493,f253])).
% 1.47/0.56  fof(f253,plain,(
% 1.47/0.56    m1_orders_2(sK4,sK0,k1_xboole_0) | ~spl6_21),
% 1.47/0.56    inference(avatar_component_clause,[],[f251])).
% 1.47/0.56  fof(f251,plain,(
% 1.47/0.56    spl6_21 <=> m1_orders_2(sK4,sK0,k1_xboole_0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.47/0.56  fof(f493,plain,(
% 1.47/0.56    ( ! [X1] : (~m1_orders_2(X1,sK0,k1_xboole_0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_28)),
% 1.47/0.56    inference(subsumption_resolution,[],[f492,f64])).
% 1.47/0.56  fof(f492,plain,(
% 1.47/0.56    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_28)),
% 1.47/0.56    inference(subsumption_resolution,[],[f491,f84])).
% 1.47/0.56  fof(f491,plain,(
% 1.47/0.56    ( ! [X1] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_28)),
% 1.47/0.56    inference(subsumption_resolution,[],[f490,f79])).
% 1.47/0.56  fof(f490,plain,(
% 1.47/0.56    ( ! [X1] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_28)),
% 1.47/0.56    inference(subsumption_resolution,[],[f489,f74])).
% 1.47/0.56  fof(f489,plain,(
% 1.47/0.56    ( ! [X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_28)),
% 1.47/0.56    inference(subsumption_resolution,[],[f480,f69])).
% 1.47/0.56  fof(f480,plain,(
% 1.47/0.56    ( ! [X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,sK0,k1_xboole_0)) ) | ~spl6_28),
% 1.47/0.56    inference(resolution,[],[f380,f56])).
% 1.47/0.56  fof(f56,plain,(
% 1.47/0.56    ( ! [X2,X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,k1_xboole_0)) )),
% 1.47/0.56    inference(equality_resolution,[],[f49])).
% 1.47/0.56  fof(f49,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X1 | k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f18])).
% 1.47/0.56  fof(f18,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.47/0.56    inference(flattening,[],[f17])).
% 1.47/0.56  fof(f17,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).
% 1.47/0.56  fof(f380,plain,(
% 1.47/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_28),
% 1.47/0.56    inference(avatar_component_clause,[],[f378])).
% 1.47/0.56  fof(f378,plain,(
% 1.47/0.56    spl6_28 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.47/0.56  fof(f444,plain,(
% 1.47/0.56    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_13 | ~spl6_14 | spl6_18 | spl6_29),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f443])).
% 1.47/0.56  fof(f443,plain,(
% 1.47/0.56    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_13 | ~spl6_14 | spl6_18 | spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f442,f145])).
% 1.47/0.56  fof(f145,plain,(
% 1.47/0.56    m1_orders_2(sK4,sK0,sK3) | ~spl6_10),
% 1.47/0.56    inference(avatar_component_clause,[],[f143])).
% 1.47/0.56  fof(f143,plain,(
% 1.47/0.56    spl6_10 <=> m1_orders_2(sK4,sK0,sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.47/0.56  fof(f442,plain,(
% 1.47/0.56    ~m1_orders_2(sK4,sK0,sK3) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_13 | ~spl6_14 | spl6_18 | spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f441,f64])).
% 1.47/0.56  fof(f441,plain,(
% 1.47/0.56    v2_struct_0(sK0) | ~m1_orders_2(sK4,sK0,sK3) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_13 | ~spl6_14 | spl6_18 | spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f440,f230])).
% 1.47/0.56  fof(f230,plain,(
% 1.47/0.56    k1_xboole_0 != sK3 | spl6_18),
% 1.47/0.56    inference(avatar_component_clause,[],[f229])).
% 1.47/0.56  fof(f229,plain,(
% 1.47/0.56    spl6_18 <=> k1_xboole_0 = sK3),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.47/0.56  fof(f440,plain,(
% 1.47/0.56    k1_xboole_0 = sK3 | v2_struct_0(sK0) | ~m1_orders_2(sK4,sK0,sK3) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_13 | ~spl6_14 | spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f439,f160])).
% 1.47/0.56  fof(f439,plain,(
% 1.47/0.56    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | v2_struct_0(sK0) | ~m1_orders_2(sK4,sK0,sK3) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f438,f165])).
% 1.47/0.56  fof(f438,plain,(
% 1.47/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | v2_struct_0(sK0) | ~m1_orders_2(sK4,sK0,sK3) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f437,f84])).
% 1.47/0.56  fof(f437,plain,(
% 1.47/0.56    ~l1_orders_2(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | v2_struct_0(sK0) | ~m1_orders_2(sK4,sK0,sK3) | (~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f436,f79])).
% 1.47/0.56  fof(f436,plain,(
% 1.47/0.56    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | v2_struct_0(sK0) | ~m1_orders_2(sK4,sK0,sK3) | (~spl6_2 | ~spl6_3 | spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f435,f74])).
% 1.47/0.56  fof(f435,plain,(
% 1.47/0.56    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | v2_struct_0(sK0) | ~m1_orders_2(sK4,sK0,sK3) | (~spl6_2 | spl6_29)),
% 1.47/0.56    inference(subsumption_resolution,[],[f430,f69])).
% 1.47/0.56  fof(f430,plain,(
% 1.47/0.56    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | v2_struct_0(sK0) | ~m1_orders_2(sK4,sK0,sK3) | spl6_29),
% 1.47/0.56    inference(resolution,[],[f425,f44])).
% 1.47/0.56  fof(f44,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | v2_struct_0(X0) | ~m1_orders_2(X2,X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f18])).
% 1.47/0.56  fof(f425,plain,(
% 1.47/0.56    ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | spl6_29),
% 1.47/0.56    inference(avatar_component_clause,[],[f423])).
% 1.47/0.56  fof(f381,plain,(
% 1.47/0.56    spl6_28 | ~spl6_26),
% 1.47/0.56    inference(avatar_split_clause,[],[f376,f321,f378])).
% 1.47/0.56  fof(f321,plain,(
% 1.47/0.56    spl6_26 <=> r1_tarski(k1_xboole_0,u1_struct_0(sK0))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.47/0.56  fof(f376,plain,(
% 1.47/0.56    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_26),
% 1.47/0.56    inference(resolution,[],[f323,f52])).
% 1.47/0.56  fof(f323,plain,(
% 1.47/0.56    r1_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~spl6_26),
% 1.47/0.56    inference(avatar_component_clause,[],[f321])).
% 1.47/0.56  fof(f324,plain,(
% 1.47/0.56    spl6_26 | ~spl6_16 | ~spl6_18),
% 1.47/0.56    inference(avatar_split_clause,[],[f317,f229,f179,f321])).
% 1.47/0.56  fof(f179,plain,(
% 1.47/0.56    spl6_16 <=> r1_tarski(sK3,u1_struct_0(sK0))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.47/0.56  fof(f317,plain,(
% 1.47/0.56    r1_tarski(k1_xboole_0,u1_struct_0(sK0)) | (~spl6_16 | ~spl6_18)),
% 1.47/0.56    inference(superposition,[],[f181,f231])).
% 1.47/0.56  fof(f231,plain,(
% 1.47/0.56    k1_xboole_0 = sK3 | ~spl6_18),
% 1.47/0.56    inference(avatar_component_clause,[],[f229])).
% 1.47/0.56  fof(f181,plain,(
% 1.47/0.56    r1_tarski(sK3,u1_struct_0(sK0)) | ~spl6_16),
% 1.47/0.56    inference(avatar_component_clause,[],[f179])).
% 1.47/0.56  fof(f254,plain,(
% 1.47/0.56    spl6_21 | ~spl6_10 | ~spl6_18),
% 1.47/0.56    inference(avatar_split_clause,[],[f234,f229,f143,f251])).
% 1.47/0.56  fof(f234,plain,(
% 1.47/0.56    m1_orders_2(sK4,sK0,k1_xboole_0) | (~spl6_10 | ~spl6_18)),
% 1.47/0.56    inference(superposition,[],[f145,f231])).
% 1.47/0.56  fof(f232,plain,(
% 1.47/0.56    spl6_17 | spl6_18 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_13 | ~spl6_14),
% 1.47/0.56    inference(avatar_split_clause,[],[f222,f163,f158,f143,f82,f77,f72,f67,f62,f229,f225])).
% 1.47/0.56  fof(f222,plain,(
% 1.47/0.56    k1_xboole_0 = sK3 | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_13 | ~spl6_14)),
% 1.47/0.56    inference(subsumption_resolution,[],[f221,f165])).
% 1.47/0.56  fof(f221,plain,(
% 1.47/0.56    k1_xboole_0 = sK3 | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_13)),
% 1.47/0.56    inference(subsumption_resolution,[],[f220,f160])).
% 1.47/0.56  fof(f220,plain,(
% 1.47/0.56    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10)),
% 1.47/0.56    inference(resolution,[],[f128,f145])).
% 1.47/0.56  fof(f128,plain,(
% 1.47/0.56    ( ! [X12,X11] : (~m1_orders_2(X12,sK0,X11) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X11 | k3_orders_2(sK0,X11,sK5(sK0,X11,X12)) = X12 | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f127,f64])).
% 1.47/0.56  fof(f127,plain,(
% 1.47/0.56    ( ! [X12,X11] : (v2_struct_0(sK0) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X11 | k3_orders_2(sK0,X11,sK5(sK0,X11,X12)) = X12 | ~m1_orders_2(X12,sK0,X11)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f126,f79])).
% 1.47/0.56  fof(f126,plain,(
% 1.47/0.56    ( ! [X12,X11] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X11 | k3_orders_2(sK0,X11,sK5(sK0,X11,X12)) = X12 | ~m1_orders_2(X12,sK0,X11)) ) | (~spl6_2 | ~spl6_3 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f125,f74])).
% 1.47/0.56  fof(f125,plain,(
% 1.47/0.56    ( ! [X12,X11] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X11 | k3_orders_2(sK0,X11,sK5(sK0,X11,X12)) = X12 | ~m1_orders_2(X12,sK0,X11)) ) | (~spl6_2 | ~spl6_5)),
% 1.47/0.56    inference(subsumption_resolution,[],[f105,f69])).
% 1.47/0.56  fof(f105,plain,(
% 1.47/0.56    ( ! [X12,X11] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X11 | k3_orders_2(sK0,X11,sK5(sK0,X11,X12)) = X12 | ~m1_orders_2(X12,sK0,X11)) ) | ~spl6_5),
% 1.47/0.56    inference(resolution,[],[f84,f46])).
% 1.47/0.56  fof(f46,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f18])).
% 1.47/0.56  fof(f182,plain,(
% 1.47/0.56    spl6_16 | ~spl6_14),
% 1.47/0.56    inference(avatar_split_clause,[],[f171,f163,f179])).
% 1.47/0.56  fof(f171,plain,(
% 1.47/0.56    r1_tarski(sK3,u1_struct_0(sK0)) | ~spl6_14),
% 1.47/0.56    inference(resolution,[],[f165,f53])).
% 1.47/0.56  fof(f53,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f2])).
% 1.47/0.56  fof(f166,plain,(
% 1.47/0.56    spl6_14),
% 1.47/0.56    inference(avatar_split_clause,[],[f32,f163])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,plain,(
% 1.47/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.47/0.56    inference(flattening,[],[f11])).
% 1.47/0.56  fof(f11,plain,(
% 1.47/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_hidden(X1,X4) & (m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,negated_conjecture,(
% 1.47/0.56    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 1.47/0.56    inference(negated_conjecture,[],[f9])).
% 1.47/0.56  fof(f9,conjecture,(
% 1.47/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).
% 1.47/0.56  fof(f161,plain,(
% 1.47/0.56    spl6_13),
% 1.47/0.56    inference(avatar_split_clause,[],[f26,f158])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f151,plain,(
% 1.47/0.56    spl6_11),
% 1.47/0.56    inference(avatar_split_clause,[],[f33,f148])).
% 1.47/0.56  fof(f33,plain,(
% 1.47/0.56    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f146,plain,(
% 1.47/0.56    spl6_10),
% 1.47/0.56    inference(avatar_split_clause,[],[f30,f143])).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    m1_orders_2(sK4,sK0,sK3)),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f141,plain,(
% 1.47/0.56    spl6_9),
% 1.47/0.56    inference(avatar_split_clause,[],[f27,f138])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    r2_orders_2(sK0,sK1,sK2)),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f100,plain,(
% 1.47/0.56    ~spl6_8),
% 1.47/0.56    inference(avatar_split_clause,[],[f31,f97])).
% 1.47/0.56  fof(f31,plain,(
% 1.47/0.56    ~r2_hidden(sK1,sK4)),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f95,plain,(
% 1.47/0.56    spl6_7),
% 1.47/0.56    inference(avatar_split_clause,[],[f29,f92])).
% 1.47/0.56  fof(f29,plain,(
% 1.47/0.56    r2_hidden(sK2,sK4)),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f90,plain,(
% 1.47/0.56    spl6_6),
% 1.47/0.56    inference(avatar_split_clause,[],[f28,f87])).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    r2_hidden(sK1,sK3)),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f85,plain,(
% 1.47/0.56    spl6_5),
% 1.47/0.56    inference(avatar_split_clause,[],[f39,f82])).
% 1.47/0.56  fof(f39,plain,(
% 1.47/0.56    l1_orders_2(sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f80,plain,(
% 1.47/0.56    spl6_4),
% 1.47/0.56    inference(avatar_split_clause,[],[f38,f77])).
% 1.47/0.56  fof(f38,plain,(
% 1.47/0.56    v5_orders_2(sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f75,plain,(
% 1.47/0.56    spl6_3),
% 1.47/0.56    inference(avatar_split_clause,[],[f37,f72])).
% 1.47/0.56  fof(f37,plain,(
% 1.47/0.56    v4_orders_2(sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f70,plain,(
% 1.47/0.56    spl6_2),
% 1.47/0.56    inference(avatar_split_clause,[],[f36,f67])).
% 1.47/0.56  fof(f36,plain,(
% 1.47/0.56    v3_orders_2(sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f65,plain,(
% 1.47/0.56    ~spl6_1),
% 1.47/0.56    inference(avatar_split_clause,[],[f35,f62])).
% 1.47/0.56  fof(f35,plain,(
% 1.47/0.56    ~v2_struct_0(sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (3758)------------------------------
% 1.47/0.56  % (3758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (3758)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (3758)Memory used [KB]: 11129
% 1.47/0.56  % (3758)Time elapsed: 0.147 s
% 1.47/0.56  % (3758)------------------------------
% 1.47/0.56  % (3758)------------------------------
% 1.47/0.56  % (3754)Success in time 0.205 s
%------------------------------------------------------------------------------
