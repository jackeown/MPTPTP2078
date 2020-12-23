%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:54 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 380 expanded)
%              Number of leaves         :   45 ( 152 expanded)
%              Depth                    :   10
%              Number of atoms          :  756 (2369 expanded)
%              Number of equality atoms :   29 (  57 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f618,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f108,f112,f116,f120,f124,f128,f132,f136,f140,f144,f157,f166,f175,f182,f186,f189,f417,f429,f477,f489,f504,f523,f526,f569,f574,f616])).

fof(f616,plain,
    ( ~ spl8_3
    | spl8_12
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f615,f567,f155,f110])).

fof(f110,plain,
    ( spl8_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f155,plain,
    ( spl8_12
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f567,plain,
    ( spl8_64
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f615,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_64 ),
    inference(duplicate_literal_removal,[],[f611])).

fof(f611,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_64 ),
    inference(resolution,[],[f580,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f580,plain,
    ( ! [X3] :
        ( r2_hidden(sK6(u1_struct_0(sK0),X3),sK1)
        | u1_struct_0(sK0) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_64 ),
    inference(resolution,[],[f568,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f568,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f567])).

fof(f574,plain,(
    ~ spl8_63 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | ~ spl8_63 ),
    inference(resolution,[],[f570,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f570,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4(X0)))
    | ~ spl8_63 ),
    inference(resolution,[],[f565,f85])).

fof(f85,plain,(
    ! [X0] : v1_xboole_0(sK4(X0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4(X0))
      & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f565,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) )
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f564])).

fof(f564,plain,
    ( spl8_63
  <=> ! [X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f569,plain,
    ( spl8_63
    | spl8_64
    | ~ spl8_52
    | ~ spl8_57 ),
    inference(avatar_split_clause,[],[f561,f521,f487,f567,f564])).

fof(f487,plain,
    ( spl8_52
  <=> ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f521,plain,
    ( spl8_57
  <=> ! [X3] :
        ( r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k3_yellow_0(sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f561,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_xboole_0(X1)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) )
    | ~ spl8_52
    | ~ spl8_57 ),
    inference(resolution,[],[f533,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f97,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f533,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_52
    | ~ spl8_57 ),
    inference(duplicate_literal_removal,[],[f528])).

fof(f528,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_52
    | ~ spl8_57 ),
    inference(resolution,[],[f522,f488])).

fof(f488,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f487])).

fof(f522,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,sK1) )
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f521])).

fof(f526,plain,
    ( ~ spl8_6
    | spl8_56 ),
    inference(avatar_split_clause,[],[f524,f518,f122])).

fof(f122,plain,
    ( spl8_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f518,plain,
    ( spl8_56
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f524,plain,
    ( ~ l1_orders_2(sK0)
    | spl8_56 ),
    inference(resolution,[],[f519,f146])).

fof(f146,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f88,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f519,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | spl8_56 ),
    inference(avatar_component_clause,[],[f518])).

fof(f523,plain,
    ( ~ spl8_56
    | spl8_57
    | ~ spl8_2
    | ~ spl8_53 ),
    inference(avatar_split_clause,[],[f514,f502,f103,f521,f518])).

fof(f103,plain,
    ( spl8_2
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f502,plain,
    ( spl8_53
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f514,plain,
    ( ! [X3] :
        ( r2_hidden(X3,sK1)
        | ~ r1_orders_2(sK0,k3_yellow_0(sK0),X3)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_53 ),
    inference(resolution,[],[f503,f104])).

fof(f104,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f503,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f502])).

fof(f504,plain,
    ( ~ spl8_3
    | spl8_53
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f492,f122,f114,f502,f110])).

fof(f114,plain,
    ( spl8_4
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f492,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK1) )
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f469,f115])).

fof(f115,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f469,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X2,sK0)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl8_6 ),
    inference(resolution,[],[f74,f123])).

fof(f123,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f74,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK2(X0,X1),X3)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f489,plain,
    ( ~ spl8_6
    | spl8_52
    | ~ spl8_46
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f485,f475,f427,f487,f122])).

fof(f427,plain,
    ( spl8_46
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f475,plain,
    ( spl8_50
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,k5_waybel_0(sK0,X2)))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f485,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_46
    | ~ spl8_50 ),
    inference(superposition,[],[f480,f73])).

fof(f480,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0)) )
    | ~ spl8_46
    | ~ spl8_50 ),
    inference(duplicate_literal_removal,[],[f479])).

fof(f479,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_46
    | ~ spl8_50 ),
    inference(superposition,[],[f476,f428])).

fof(f428,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f427])).

fof(f476,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,k5_waybel_0(sK0,X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X2)) )
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f475])).

fof(f477,plain,
    ( spl8_11
    | ~ spl8_8
    | ~ spl8_7
    | ~ spl8_6
    | spl8_50
    | ~ spl8_6
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f473,f415,f122,f475,f122,f126,f130,f142])).

fof(f142,plain,
    ( spl8_11
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f130,plain,
    ( spl8_8
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f126,plain,
    ( spl8_7
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f415,plain,
    ( spl8_44
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f473,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X2))
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,k5_waybel_0(sK0,X2)))
        | ~ l1_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_6
    | ~ spl8_44 ),
    inference(resolution,[],[f419,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f419,plain,
    ( ! [X2,X1] :
        ( ~ r1_yellow_0(sK0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tarski(X2,k5_waybel_0(sK0,X1))
        | r1_orders_2(sK0,k1_yellow_0(sK0,X2),k1_yellow_0(sK0,k5_waybel_0(sK0,X1))) )
    | ~ spl8_6
    | ~ spl8_44 ),
    inference(resolution,[],[f416,f381])).

fof(f381,plain,
    ( ! [X0,X1] :
        ( ~ r1_yellow_0(sK0,X0)
        | ~ r1_yellow_0(sK0,X1)
        | ~ r1_tarski(X1,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X0)) )
    | ~ spl8_6 ),
    inference(resolution,[],[f80,f123])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f416,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK0,k5_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f415])).

fof(f429,plain,
    ( spl8_11
    | ~ spl8_10
    | ~ spl8_8
    | ~ spl8_6
    | spl8_46
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f425,f134,f427,f122,f130,f138,f142])).

fof(f138,plain,
    ( spl8_10
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f134,plain,
    ( spl8_9
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f425,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_9 ),
    inference(resolution,[],[f82,f135])).

fof(f135,plain,
    ( v4_orders_2(sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

fof(f417,plain,
    ( spl8_11
    | ~ spl8_10
    | ~ spl8_8
    | ~ spl8_6
    | spl8_44
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f412,f134,f415,f122,f130,f138,f142])).

fof(f412,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | r1_yellow_0(sK0,k5_waybel_0(sK0,X0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_9 ),
    inference(resolution,[],[f81,f135])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f189,plain,
    ( ~ spl8_13
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f187,f168,f164])).

fof(f164,plain,
    ( spl8_13
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f168,plain,
    ( spl8_14
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f187,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl8_14 ),
    inference(resolution,[],[f185,f98])).

fof(f98,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f185,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f168])).

fof(f186,plain,
    ( spl8_14
    | ~ spl8_1
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f184,f155,f100,f168])).

fof(f100,plain,
    ( spl8_1
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f184,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_1
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f106,f156])).

fof(f156,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f106,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f182,plain,
    ( spl8_2
    | spl8_5
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f181,f173,f118,f103])).

fof(f118,plain,
    ( spl8_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f173,plain,
    ( spl8_15
  <=> m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f181,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | spl8_5
    | ~ spl8_15 ),
    inference(resolution,[],[f174,f147])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(X0,sK1) )
    | spl8_5 ),
    inference(resolution,[],[f89,f119])).

fof(f119,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f174,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f175,plain,
    ( ~ spl8_6
    | spl8_15
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f161,f155,f173,f122])).

fof(f161,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl8_12 ),
    inference(superposition,[],[f146,f156])).

fof(f166,plain,
    ( spl8_13
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f159,f155,f110,f164])).

fof(f159,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(superposition,[],[f111,f156])).

fof(f111,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f157,plain,
    ( ~ spl8_3
    | spl8_12
    | spl8_1 ),
    inference(avatar_split_clause,[],[f149,f100,f155,f110])).

fof(f149,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_1 ),
    inference(resolution,[],[f93,f101])).

fof(f101,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f144,plain,(
    ~ spl8_11 ),
    inference(avatar_split_clause,[],[f61,f142])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
    & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | v1_subset_1(sK1,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
          & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
            | v1_subset_1(X1,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK0),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
        & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
          | v1_subset_1(X1,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
      & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | v1_subset_1(sK1,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f140,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f62,f138])).

fof(f62,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f136,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f63,f134])).

fof(f63,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f132,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f64,f130])).

fof(f64,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f128,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f65,f126])).

fof(f65,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f124,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f66,f122])).

fof(f66,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f120,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f67,f118])).

fof(f67,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f116,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f68,f114])).

fof(f68,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f112,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f69,f110])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f108,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f70,f103,f100])).

fof(f70,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f105,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f71,f103,f100])).

fof(f71,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (21727)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (21735)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (21743)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (21732)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.52  % (21722)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.52  % (21720)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.53  % (21747)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.53  % (21721)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.53  % (21729)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.53  % (21739)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.53  % (21724)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  % (21736)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.53  % (21725)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.53  % (21723)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.40/0.53  % (21742)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.40/0.54  % (21728)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.54  % (21733)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.54  % (21731)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.54  % (21734)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.54  % (21730)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.54  % (21728)Refutation not found, incomplete strategy% (21728)------------------------------
% 1.40/0.54  % (21728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (21728)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (21728)Memory used [KB]: 10746
% 1.40/0.54  % (21728)Time elapsed: 0.136 s
% 1.40/0.54  % (21728)------------------------------
% 1.40/0.54  % (21728)------------------------------
% 1.40/0.54  % (21740)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.54  % (21749)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.54  % (21746)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.54  % (21745)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.54  % (21722)Refutation not found, incomplete strategy% (21722)------------------------------
% 1.40/0.54  % (21722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (21722)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (21722)Memory used [KB]: 11001
% 1.40/0.55  % (21722)Time elapsed: 0.143 s
% 1.40/0.55  % (21722)------------------------------
% 1.40/0.55  % (21722)------------------------------
% 1.40/0.55  % (21746)Refutation not found, incomplete strategy% (21746)------------------------------
% 1.40/0.55  % (21746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (21746)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (21746)Memory used [KB]: 10874
% 1.40/0.55  % (21746)Time elapsed: 0.151 s
% 1.40/0.55  % (21746)------------------------------
% 1.40/0.55  % (21746)------------------------------
% 1.40/0.55  % (21741)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.55  % (21738)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.55  % (21737)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.55  % (21726)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.55  % (21739)Refutation found. Thanks to Tanya!
% 1.40/0.55  % SZS status Theorem for theBenchmark
% 1.40/0.55  % (21748)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.56  % SZS output start Proof for theBenchmark
% 1.40/0.56  fof(f618,plain,(
% 1.40/0.56    $false),
% 1.40/0.56    inference(avatar_sat_refutation,[],[f105,f108,f112,f116,f120,f124,f128,f132,f136,f140,f144,f157,f166,f175,f182,f186,f189,f417,f429,f477,f489,f504,f523,f526,f569,f574,f616])).
% 1.40/0.56  fof(f616,plain,(
% 1.40/0.56    ~spl8_3 | spl8_12 | ~spl8_64),
% 1.40/0.56    inference(avatar_split_clause,[],[f615,f567,f155,f110])).
% 1.40/0.56  fof(f110,plain,(
% 1.40/0.56    spl8_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.40/0.56  fof(f155,plain,(
% 1.40/0.56    spl8_12 <=> u1_struct_0(sK0) = sK1),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.40/0.56  fof(f567,plain,(
% 1.40/0.56    spl8_64 <=> ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).
% 1.40/0.56  fof(f615,plain,(
% 1.40/0.56    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_64),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f611])).
% 1.40/0.56  fof(f611,plain,(
% 1.40/0.56    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_64),
% 1.40/0.56    inference(resolution,[],[f580,f91])).
% 1.40/0.56  fof(f91,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f57])).
% 1.40/0.56  fof(f57,plain,(
% 1.40/0.56    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f56])).
% 1.40/0.56  fof(f56,plain,(
% 1.40/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),X0)))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f36,plain,(
% 1.40/0.56    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.56    inference(flattening,[],[f35])).
% 1.40/0.56  fof(f35,plain,(
% 1.40/0.56    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f3])).
% 1.40/0.56  fof(f3,axiom,(
% 1.40/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 1.40/0.56  fof(f580,plain,(
% 1.40/0.56    ( ! [X3] : (r2_hidden(sK6(u1_struct_0(sK0),X3),sK1) | u1_struct_0(sK0) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_64),
% 1.40/0.56    inference(resolution,[],[f568,f90])).
% 1.40/0.56  fof(f90,plain,(
% 1.40/0.56    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f57])).
% 1.40/0.56  fof(f568,plain,(
% 1.40/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | ~spl8_64),
% 1.40/0.56    inference(avatar_component_clause,[],[f567])).
% 1.40/0.56  fof(f574,plain,(
% 1.40/0.56    ~spl8_63),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f572])).
% 1.40/0.56  fof(f572,plain,(
% 1.40/0.56    $false | ~spl8_63),
% 1.40/0.56    inference(resolution,[],[f570,f72])).
% 1.40/0.56  fof(f72,plain,(
% 1.40/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f4])).
% 1.40/0.56  fof(f4,axiom,(
% 1.40/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.40/0.56  fof(f570,plain,(
% 1.40/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4(X0)))) ) | ~spl8_63),
% 1.40/0.56    inference(resolution,[],[f565,f85])).
% 1.40/0.56  fof(f85,plain,(
% 1.40/0.56    ( ! [X0] : (v1_xboole_0(sK4(X0))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f53])).
% 1.40/0.56  fof(f53,plain,(
% 1.40/0.56    ! [X0] : (v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)))),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2,f52])).
% 1.40/0.56  fof(f52,plain,(
% 1.40/0.56    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0))))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f2,axiom,(
% 1.40/0.56    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 1.40/0.56  fof(f565,plain,(
% 1.40/0.56    ( ! [X1] : (~v1_xboole_0(X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) ) | ~spl8_63),
% 1.40/0.56    inference(avatar_component_clause,[],[f564])).
% 1.40/0.56  fof(f564,plain,(
% 1.40/0.56    spl8_63 <=> ! [X1] : (~v1_xboole_0(X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).
% 1.40/0.56  fof(f569,plain,(
% 1.40/0.56    spl8_63 | spl8_64 | ~spl8_52 | ~spl8_57),
% 1.40/0.56    inference(avatar_split_clause,[],[f561,f521,f487,f567,f564])).
% 1.40/0.56  fof(f487,plain,(
% 1.40/0.56    spl8_52 <=> ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 1.40/0.56  fof(f521,plain,(
% 1.40/0.56    spl8_57 <=> ! [X3] : (r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k3_yellow_0(sK0),X3))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 1.40/0.56  fof(f561,plain,(
% 1.40/0.56    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_xboole_0(X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) ) | (~spl8_52 | ~spl8_57)),
% 1.40/0.56    inference(resolution,[],[f533,f148])).
% 1.40/0.56  fof(f148,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.40/0.56    inference(resolution,[],[f97,f94])).
% 1.40/0.56  fof(f94,plain,(
% 1.40/0.56    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f60])).
% 1.40/0.56  fof(f60,plain,(
% 1.40/0.56    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f59])).
% 1.40/0.56  fof(f59,plain,(
% 1.40/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f38,plain,(
% 1.40/0.56    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f18])).
% 1.40/0.56  fof(f18,plain,(
% 1.40/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.40/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.40/0.56  fof(f1,axiom,(
% 1.40/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.56  fof(f97,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f41])).
% 1.40/0.56  fof(f41,plain,(
% 1.40/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.40/0.56    inference(ennf_transformation,[],[f8])).
% 1.40/0.56  fof(f8,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.40/0.56  fof(f533,plain,(
% 1.40/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_52 | ~spl8_57)),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f528])).
% 1.40/0.56  fof(f528,plain,(
% 1.40/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_52 | ~spl8_57)),
% 1.40/0.56    inference(resolution,[],[f522,f488])).
% 1.40/0.56  fof(f488,plain,(
% 1.40/0.56    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_52),
% 1.40/0.56    inference(avatar_component_clause,[],[f487])).
% 1.40/0.56  fof(f522,plain,(
% 1.40/0.56    ( ! [X3] : (~r1_orders_2(sK0,k3_yellow_0(sK0),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,sK1)) ) | ~spl8_57),
% 1.40/0.56    inference(avatar_component_clause,[],[f521])).
% 1.40/0.56  fof(f526,plain,(
% 1.40/0.56    ~spl8_6 | spl8_56),
% 1.40/0.56    inference(avatar_split_clause,[],[f524,f518,f122])).
% 1.40/0.56  fof(f122,plain,(
% 1.40/0.56    spl8_6 <=> l1_orders_2(sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.40/0.56  fof(f518,plain,(
% 1.40/0.56    spl8_56 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).
% 1.40/0.56  fof(f524,plain,(
% 1.40/0.56    ~l1_orders_2(sK0) | spl8_56),
% 1.40/0.56    inference(resolution,[],[f519,f146])).
% 1.40/0.56  fof(f146,plain,(
% 1.40/0.56    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f145])).
% 1.40/0.56  fof(f145,plain,(
% 1.40/0.56    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~l1_orders_2(X0)) )),
% 1.40/0.56    inference(superposition,[],[f88,f73])).
% 1.40/0.56  fof(f73,plain,(
% 1.40/0.56    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f23])).
% 1.40/0.56  fof(f23,plain,(
% 1.40/0.56    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f9])).
% 1.40/0.56  fof(f9,axiom,(
% 1.40/0.56    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.40/0.56  fof(f88,plain,(
% 1.40/0.56    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f32])).
% 1.40/0.56  fof(f32,plain,(
% 1.40/0.56    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f10])).
% 1.40/0.56  fof(f10,axiom,(
% 1.40/0.56    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 1.40/0.56  fof(f519,plain,(
% 1.40/0.56    ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | spl8_56),
% 1.40/0.56    inference(avatar_component_clause,[],[f518])).
% 1.40/0.56  fof(f523,plain,(
% 1.40/0.56    ~spl8_56 | spl8_57 | ~spl8_2 | ~spl8_53),
% 1.40/0.56    inference(avatar_split_clause,[],[f514,f502,f103,f521,f518])).
% 1.40/0.56  fof(f103,plain,(
% 1.40/0.56    spl8_2 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.40/0.56  fof(f502,plain,(
% 1.40/0.56    spl8_53 <=> ! [X1,X0] : (~r2_hidden(X0,sK1) | r2_hidden(X1,sK1) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 1.40/0.56  fof(f514,plain,(
% 1.40/0.56    ( ! [X3] : (r2_hidden(X3,sK1) | ~r1_orders_2(sK0,k3_yellow_0(sK0),X3) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_53)),
% 1.40/0.56    inference(resolution,[],[f503,f104])).
% 1.40/0.56  fof(f104,plain,(
% 1.40/0.56    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl8_2),
% 1.40/0.56    inference(avatar_component_clause,[],[f103])).
% 1.40/0.56  fof(f503,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | r2_hidden(X1,sK1) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl8_53),
% 1.40/0.56    inference(avatar_component_clause,[],[f502])).
% 1.40/0.56  fof(f504,plain,(
% 1.40/0.56    ~spl8_3 | spl8_53 | ~spl8_4 | ~spl8_6),
% 1.40/0.56    inference(avatar_split_clause,[],[f492,f122,f114,f502,f110])).
% 1.40/0.56  fof(f114,plain,(
% 1.40/0.56    spl8_4 <=> v13_waybel_0(sK1,sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.40/0.56  fof(f492,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK1)) ) | (~spl8_4 | ~spl8_6)),
% 1.40/0.56    inference(resolution,[],[f469,f115])).
% 1.40/0.56  fof(f115,plain,(
% 1.40/0.56    v13_waybel_0(sK1,sK0) | ~spl8_4),
% 1.40/0.56    inference(avatar_component_clause,[],[f114])).
% 1.40/0.56  fof(f469,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (~v13_waybel_0(X2,sK0) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl8_6),
% 1.40/0.56    inference(resolution,[],[f74,f123])).
% 1.40/0.56  fof(f123,plain,(
% 1.40/0.56    l1_orders_2(sK0) | ~spl8_6),
% 1.40/0.56    inference(avatar_component_clause,[],[f122])).
% 1.40/0.56  fof(f74,plain,(
% 1.40/0.56    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f51])).
% 1.40/0.56  fof(f51,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f50,f49])).
% 1.40/0.56  fof(f49,plain,(
% 1.40/0.56    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f50,plain,(
% 1.40/0.56    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f48,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.40/0.56    inference(rectify,[],[f47])).
% 1.40/0.56  fof(f47,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.40/0.56    inference(nnf_transformation,[],[f25])).
% 1.40/0.56  fof(f25,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.40/0.56    inference(flattening,[],[f24])).
% 1.40/0.56  fof(f24,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f13])).
% 1.40/0.56  fof(f13,axiom,(
% 1.40/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.40/0.56  fof(f489,plain,(
% 1.40/0.56    ~spl8_6 | spl8_52 | ~spl8_46 | ~spl8_50),
% 1.40/0.56    inference(avatar_split_clause,[],[f485,f475,f427,f487,f122])).
% 1.40/0.56  fof(f427,plain,(
% 1.40/0.56    spl8_46 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 1.40/0.56  fof(f475,plain,(
% 1.40/0.56    spl8_50 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,k5_waybel_0(sK0,X2))) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X2)))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 1.40/0.56  fof(f485,plain,(
% 1.40/0.56    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0)) | ~l1_orders_2(sK0)) ) | (~spl8_46 | ~spl8_50)),
% 1.40/0.56    inference(superposition,[],[f480,f73])).
% 1.40/0.56  fof(f480,plain,(
% 1.40/0.56    ( ! [X0] : (r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0))) ) | (~spl8_46 | ~spl8_50)),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f479])).
% 1.40/0.56  fof(f479,plain,(
% 1.40/0.56    ( ! [X0] : (r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_46 | ~spl8_50)),
% 1.40/0.56    inference(superposition,[],[f476,f428])).
% 1.40/0.56  fof(f428,plain,(
% 1.40/0.56    ( ! [X0] : (k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_46),
% 1.40/0.56    inference(avatar_component_clause,[],[f427])).
% 1.40/0.56  fof(f476,plain,(
% 1.40/0.56    ( ! [X2] : (r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,k5_waybel_0(sK0,X2))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X2))) ) | ~spl8_50),
% 1.40/0.56    inference(avatar_component_clause,[],[f475])).
% 1.40/0.56  fof(f477,plain,(
% 1.40/0.56    spl8_11 | ~spl8_8 | ~spl8_7 | ~spl8_6 | spl8_50 | ~spl8_6 | ~spl8_44),
% 1.40/0.56    inference(avatar_split_clause,[],[f473,f415,f122,f475,f122,f126,f130,f142])).
% 1.40/0.56  fof(f142,plain,(
% 1.40/0.56    spl8_11 <=> v2_struct_0(sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.40/0.56  fof(f130,plain,(
% 1.40/0.56    spl8_8 <=> v5_orders_2(sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.40/0.56  fof(f126,plain,(
% 1.40/0.56    spl8_7 <=> v1_yellow_0(sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.40/0.56  fof(f415,plain,(
% 1.40/0.56    spl8_44 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_yellow_0(sK0,k5_waybel_0(sK0,X0)))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 1.40/0.56  fof(f473,plain,(
% 1.40/0.56    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_tarski(k1_xboole_0,k5_waybel_0(sK0,X2)) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,k5_waybel_0(sK0,X2))) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl8_6 | ~spl8_44)),
% 1.40/0.56    inference(resolution,[],[f419,f83])).
% 1.40/0.56  fof(f83,plain,(
% 1.40/0.56    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f31])).
% 1.40/0.56  fof(f31,plain,(
% 1.40/0.56    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.40/0.56    inference(flattening,[],[f30])).
% 1.40/0.56  fof(f30,plain,(
% 1.40/0.56    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f20])).
% 1.40/0.56  fof(f20,plain,(
% 1.40/0.56    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 1.40/0.56    inference(pure_predicate_removal,[],[f12])).
% 1.40/0.56  fof(f12,axiom,(
% 1.40/0.56    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 1.40/0.56  fof(f419,plain,(
% 1.40/0.56    ( ! [X2,X1] : (~r1_yellow_0(sK0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tarski(X2,k5_waybel_0(sK0,X1)) | r1_orders_2(sK0,k1_yellow_0(sK0,X2),k1_yellow_0(sK0,k5_waybel_0(sK0,X1)))) ) | (~spl8_6 | ~spl8_44)),
% 1.40/0.56    inference(resolution,[],[f416,f381])).
% 1.40/0.56  fof(f381,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~r1_yellow_0(sK0,X0) | ~r1_yellow_0(sK0,X1) | ~r1_tarski(X1,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X0))) ) | ~spl8_6),
% 1.40/0.56    inference(resolution,[],[f80,f123])).
% 1.40/0.56  fof(f80,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f27])).
% 1.40/0.56  fof(f27,plain,(
% 1.40/0.56    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.40/0.56    inference(flattening,[],[f26])).
% 1.40/0.56  fof(f26,plain,(
% 1.40/0.56    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f11])).
% 1.40/0.56  fof(f11,axiom,(
% 1.40/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).
% 1.40/0.56  fof(f416,plain,(
% 1.40/0.56    ( ! [X0] : (r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_44),
% 1.40/0.56    inference(avatar_component_clause,[],[f415])).
% 1.40/0.56  fof(f429,plain,(
% 1.40/0.56    spl8_11 | ~spl8_10 | ~spl8_8 | ~spl8_6 | spl8_46 | ~spl8_9),
% 1.40/0.56    inference(avatar_split_clause,[],[f425,f134,f427,f122,f130,f138,f142])).
% 1.40/0.56  fof(f138,plain,(
% 1.40/0.56    spl8_10 <=> v3_orders_2(sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.40/0.56  fof(f134,plain,(
% 1.40/0.56    spl8_9 <=> v4_orders_2(sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.40/0.56  fof(f425,plain,(
% 1.40/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | k1_yellow_0(sK0,k5_waybel_0(sK0,X0)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_9),
% 1.40/0.56    inference(resolution,[],[f82,f135])).
% 1.40/0.56  fof(f135,plain,(
% 1.40/0.56    v4_orders_2(sK0) | ~spl8_9),
% 1.40/0.56    inference(avatar_component_clause,[],[f134])).
% 1.40/0.56  fof(f82,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~v4_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f29])).
% 1.40/0.56  fof(f29,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.40/0.56    inference(flattening,[],[f28])).
% 1.40/0.56  fof(f28,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f14])).
% 1.40/0.56  fof(f14,axiom,(
% 1.40/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).
% 1.40/0.56  fof(f417,plain,(
% 1.40/0.56    spl8_11 | ~spl8_10 | ~spl8_8 | ~spl8_6 | spl8_44 | ~spl8_9),
% 1.40/0.56    inference(avatar_split_clause,[],[f412,f134,f415,f122,f130,f138,f142])).
% 1.40/0.56  fof(f412,plain,(
% 1.40/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,X0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_9),
% 1.40/0.56    inference(resolution,[],[f81,f135])).
% 1.40/0.56  fof(f81,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~v4_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f29])).
% 1.40/0.56  fof(f189,plain,(
% 1.40/0.56    ~spl8_13 | ~spl8_14),
% 1.40/0.56    inference(avatar_split_clause,[],[f187,f168,f164])).
% 1.40/0.56  fof(f164,plain,(
% 1.40/0.56    spl8_13 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.40/0.56  fof(f168,plain,(
% 1.40/0.56    spl8_14 <=> v1_subset_1(sK1,sK1)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.40/0.56  fof(f187,plain,(
% 1.40/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl8_14),
% 1.40/0.56    inference(resolution,[],[f185,f98])).
% 1.40/0.56  fof(f98,plain,(
% 1.40/0.56    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 1.40/0.56    inference(equality_resolution,[],[f92])).
% 1.40/0.56  fof(f92,plain,(
% 1.40/0.56    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f58])).
% 1.40/0.56  fof(f58,plain,(
% 1.40/0.56    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.56    inference(nnf_transformation,[],[f37])).
% 1.40/0.56  fof(f37,plain,(
% 1.40/0.56    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f15])).
% 1.40/0.56  fof(f15,axiom,(
% 1.40/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.40/0.56  fof(f185,plain,(
% 1.40/0.56    v1_subset_1(sK1,sK1) | ~spl8_14),
% 1.40/0.56    inference(avatar_component_clause,[],[f168])).
% 1.40/0.56  fof(f186,plain,(
% 1.40/0.56    spl8_14 | ~spl8_1 | ~spl8_12),
% 1.40/0.56    inference(avatar_split_clause,[],[f184,f155,f100,f168])).
% 1.40/0.56  fof(f100,plain,(
% 1.40/0.56    spl8_1 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.40/0.56  fof(f184,plain,(
% 1.40/0.56    v1_subset_1(sK1,sK1) | (~spl8_1 | ~spl8_12)),
% 1.40/0.56    inference(forward_demodulation,[],[f106,f156])).
% 1.40/0.56  fof(f156,plain,(
% 1.40/0.56    u1_struct_0(sK0) = sK1 | ~spl8_12),
% 1.40/0.56    inference(avatar_component_clause,[],[f155])).
% 1.40/0.56  fof(f106,plain,(
% 1.40/0.56    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_1),
% 1.40/0.56    inference(avatar_component_clause,[],[f100])).
% 1.40/0.56  fof(f182,plain,(
% 1.40/0.56    spl8_2 | spl8_5 | ~spl8_15),
% 1.40/0.56    inference(avatar_split_clause,[],[f181,f173,f118,f103])).
% 1.40/0.56  fof(f118,plain,(
% 1.40/0.56    spl8_5 <=> v1_xboole_0(sK1)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.40/0.56  fof(f173,plain,(
% 1.40/0.56    spl8_15 <=> m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.40/0.56  fof(f181,plain,(
% 1.40/0.56    r2_hidden(k3_yellow_0(sK0),sK1) | (spl8_5 | ~spl8_15)),
% 1.40/0.56    inference(resolution,[],[f174,f147])).
% 1.40/0.56  fof(f147,plain,(
% 1.40/0.56    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(X0,sK1)) ) | spl8_5),
% 1.40/0.56    inference(resolution,[],[f89,f119])).
% 1.40/0.56  fof(f119,plain,(
% 1.40/0.56    ~v1_xboole_0(sK1) | spl8_5),
% 1.40/0.56    inference(avatar_component_clause,[],[f118])).
% 1.40/0.56  fof(f89,plain,(
% 1.40/0.56    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f34])).
% 1.40/0.56  fof(f34,plain,(
% 1.40/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.40/0.56    inference(flattening,[],[f33])).
% 1.40/0.56  fof(f33,plain,(
% 1.40/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.40/0.56    inference(ennf_transformation,[],[f6])).
% 1.40/0.56  fof(f6,axiom,(
% 1.40/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.40/0.56  fof(f174,plain,(
% 1.40/0.56    m1_subset_1(k3_yellow_0(sK0),sK1) | ~spl8_15),
% 1.40/0.56    inference(avatar_component_clause,[],[f173])).
% 1.40/0.56  fof(f175,plain,(
% 1.40/0.56    ~spl8_6 | spl8_15 | ~spl8_12),
% 1.40/0.56    inference(avatar_split_clause,[],[f161,f155,f173,f122])).
% 1.40/0.56  fof(f161,plain,(
% 1.40/0.56    m1_subset_1(k3_yellow_0(sK0),sK1) | ~l1_orders_2(sK0) | ~spl8_12),
% 1.40/0.56    inference(superposition,[],[f146,f156])).
% 1.40/0.56  fof(f166,plain,(
% 1.40/0.56    spl8_13 | ~spl8_3 | ~spl8_12),
% 1.40/0.56    inference(avatar_split_clause,[],[f159,f155,f110,f164])).
% 1.40/0.56  fof(f159,plain,(
% 1.40/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl8_3 | ~spl8_12)),
% 1.40/0.56    inference(superposition,[],[f111,f156])).
% 1.40/0.56  fof(f111,plain,(
% 1.40/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_3),
% 1.40/0.56    inference(avatar_component_clause,[],[f110])).
% 1.40/0.56  fof(f157,plain,(
% 1.40/0.56    ~spl8_3 | spl8_12 | spl8_1),
% 1.40/0.56    inference(avatar_split_clause,[],[f149,f100,f155,f110])).
% 1.40/0.56  fof(f149,plain,(
% 1.40/0.56    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl8_1),
% 1.40/0.56    inference(resolution,[],[f93,f101])).
% 1.40/0.56  fof(f101,plain,(
% 1.40/0.56    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl8_1),
% 1.40/0.56    inference(avatar_component_clause,[],[f100])).
% 1.40/0.56  fof(f93,plain,(
% 1.40/0.56    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f58])).
% 1.40/0.56  fof(f144,plain,(
% 1.40/0.56    ~spl8_11),
% 1.40/0.56    inference(avatar_split_clause,[],[f61,f142])).
% 1.40/0.56  fof(f61,plain,(
% 1.40/0.56    ~v2_struct_0(sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f46,plain,(
% 1.40/0.56    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f45,f44])).
% 1.40/0.56  fof(f44,plain,(
% 1.40/0.56    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f45,plain,(
% 1.40/0.56    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f43,plain,(
% 1.40/0.56    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.40/0.56    inference(flattening,[],[f42])).
% 1.40/0.56  fof(f42,plain,(
% 1.40/0.56    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.40/0.56    inference(nnf_transformation,[],[f22])).
% 1.40/0.56  fof(f22,plain,(
% 1.40/0.56    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.40/0.56    inference(flattening,[],[f21])).
% 1.40/0.56  fof(f21,plain,(
% 1.40/0.56    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f19])).
% 1.40/0.56  fof(f19,plain,(
% 1.40/0.56    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.40/0.56    inference(pure_predicate_removal,[],[f17])).
% 1.40/0.56  fof(f17,negated_conjecture,(
% 1.40/0.56    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.40/0.56    inference(negated_conjecture,[],[f16])).
% 1.40/0.56  fof(f16,conjecture,(
% 1.40/0.56    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.40/0.56  fof(f140,plain,(
% 1.40/0.56    spl8_10),
% 1.40/0.56    inference(avatar_split_clause,[],[f62,f138])).
% 1.40/0.56  fof(f62,plain,(
% 1.40/0.56    v3_orders_2(sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f136,plain,(
% 1.40/0.56    spl8_9),
% 1.40/0.56    inference(avatar_split_clause,[],[f63,f134])).
% 1.40/0.56  fof(f63,plain,(
% 1.40/0.56    v4_orders_2(sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f132,plain,(
% 1.40/0.56    spl8_8),
% 1.40/0.56    inference(avatar_split_clause,[],[f64,f130])).
% 1.40/0.56  fof(f64,plain,(
% 1.40/0.56    v5_orders_2(sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f128,plain,(
% 1.40/0.56    spl8_7),
% 1.40/0.56    inference(avatar_split_clause,[],[f65,f126])).
% 1.40/0.56  fof(f65,plain,(
% 1.40/0.56    v1_yellow_0(sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f124,plain,(
% 1.40/0.56    spl8_6),
% 1.40/0.56    inference(avatar_split_clause,[],[f66,f122])).
% 1.40/0.56  fof(f66,plain,(
% 1.40/0.56    l1_orders_2(sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f120,plain,(
% 1.40/0.56    ~spl8_5),
% 1.40/0.56    inference(avatar_split_clause,[],[f67,f118])).
% 1.40/0.56  fof(f67,plain,(
% 1.40/0.56    ~v1_xboole_0(sK1)),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f116,plain,(
% 1.40/0.56    spl8_4),
% 1.40/0.56    inference(avatar_split_clause,[],[f68,f114])).
% 1.40/0.56  fof(f68,plain,(
% 1.40/0.56    v13_waybel_0(sK1,sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f112,plain,(
% 1.40/0.56    spl8_3),
% 1.40/0.56    inference(avatar_split_clause,[],[f69,f110])).
% 1.40/0.56  fof(f69,plain,(
% 1.40/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f108,plain,(
% 1.40/0.56    spl8_1 | ~spl8_2),
% 1.40/0.56    inference(avatar_split_clause,[],[f70,f103,f100])).
% 1.40/0.56  fof(f70,plain,(
% 1.40/0.56    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f105,plain,(
% 1.40/0.56    ~spl8_1 | spl8_2),
% 1.40/0.56    inference(avatar_split_clause,[],[f71,f103,f100])).
% 1.40/0.56  fof(f71,plain,(
% 1.40/0.56    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  % SZS output end Proof for theBenchmark
% 1.40/0.56  % (21739)------------------------------
% 1.40/0.56  % (21739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (21739)Termination reason: Refutation
% 1.40/0.56  
% 1.40/0.56  % (21739)Memory used [KB]: 11129
% 1.40/0.56  % (21739)Time elapsed: 0.142 s
% 1.40/0.56  % (21739)------------------------------
% 1.40/0.56  % (21739)------------------------------
% 1.40/0.56  % (21719)Success in time 0.21 s
%------------------------------------------------------------------------------
