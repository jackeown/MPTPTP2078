%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 209 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  287 ( 621 expanded)
%              Number of equality atoms :   12 (  38 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f89,f99,f102,f105,f123,f141,f179,f184])).

fof(f184,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | spl11_5
    | ~ spl11_7 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | spl11_5
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f182,f67])).

fof(f67,plain,
    ( v3_orders_2(sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl11_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f182,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl11_3
    | ~ spl11_4
    | spl11_5
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f181,f94])).

fof(f94,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl11_7
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f181,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl11_3
    | ~ spl11_4
    | spl11_5 ),
    inference(subsumption_resolution,[],[f180,f82])).

fof(f82,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl11_5
  <=> r1_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f180,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f178,f72])).

fof(f72,plain,
    ( l1_orders_2(sK0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl11_3
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f178,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK1)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl11_4 ),
    inference(resolution,[],[f172,f77])).

fof(f77,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl11_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X0,X0)
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ v3_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f171,f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_relat_1(u1_orders_2(X0)) ) ),
    inference(resolution,[],[f134,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v1_relat_1(u1_orders_2(X0)) ) ),
    inference(resolution,[],[f36,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f134,plain,(
    ! [X4,X5] : v1_relat_1(k2_zfmisc_1(X4,X5)) ),
    inference(subsumption_resolution,[],[f131,f44])).

fof(f44,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f131,plain,(
    ! [X4,X5] :
      ( sK3(k2_zfmisc_1(X4,X5)) = k4_tarski(sK7(X4,X5,sK3(k2_zfmisc_1(X4,X5))),sK8(X4,X5,sK3(k2_zfmisc_1(X4,X5))))
      | v1_relat_1(k2_zfmisc_1(X4,X5)) ) ),
    inference(resolution,[],[f56,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X0,X0)
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ v1_relat_1(u1_orders_2(X1))
      | ~ v3_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X0,X0)
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ v1_relat_1(u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(resolution,[],[f39,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X0),u1_orders_2(X1))
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ v1_relat_1(u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(resolution,[],[f32,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_orders_2)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_relat_2(X0,X1)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(k4_tarski(X2,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f179,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | spl11_5
    | ~ spl11_7 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | spl11_5
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f67,f72,f94,f82,f77,f172])).

fof(f141,plain,
    ( spl11_11
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f136,f70,f138])).

fof(f138,plain,
    ( spl11_11
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

% (28767)Refutation not found, incomplete strategy% (28767)------------------------------
% (28767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28767)Termination reason: Refutation not found, incomplete strategy

% (28767)Memory used [KB]: 10618
% (28767)Time elapsed: 0.073 s
% (28767)------------------------------
% (28767)------------------------------
fof(f136,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl11_3 ),
    inference(resolution,[],[f135,f72])).

fof(f123,plain,
    ( ~ spl11_9
    | spl11_10
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f111,f92,f120,f116])).

fof(f116,plain,
    ( spl11_9
  <=> v1_relat_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f120,plain,
    ( spl11_10
  <=> sK1 = k4_tarski(sK4(sK1),sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f111,plain,
    ( sK1 = k4_tarski(sK4(sK1),sK5(sK1))
    | ~ v1_relat_1(u1_struct_0(sK0))
    | ~ spl11_7 ),
    inference(resolution,[],[f42,f94])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_tarski(sK4(X1),sK5(X1)) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,
    ( spl11_1
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f103,f62])).

fof(f62,plain,
    ( ~ v2_struct_0(sK0)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl11_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f103,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f101,f88])).

fof(f88,plain,
    ( l1_struct_0(sK0)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl11_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f101,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_8 ),
    inference(resolution,[],[f98,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f98,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl11_8
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f102,plain,
    ( spl11_1
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl11_1
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f62,f88,f98,f41])).

fof(f99,plain,
    ( spl11_7
    | spl11_8
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f90,f75,f96,f92])).

fof(f90,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl11_4 ),
    inference(resolution,[],[f45,f77])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f89,plain,
    ( spl11_6
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f84,f70,f86])).

fof(f84,plain,
    ( l1_struct_0(sK0)
    | ~ spl11_3 ),
    inference(resolution,[],[f35,f72])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f83,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f27,f80])).

fof(f27,plain,(
    ~ r1_orders_2(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_orders_2(X0,X1,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r1_orders_2(X0,X1,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f78,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f26,f75])).

fof(f26,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (28755)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (28767)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (28755)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f89,f99,f102,f105,f123,f141,f179,f184])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ~spl11_2 | ~spl11_3 | ~spl11_4 | spl11_5 | ~spl11_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f183])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    $false | (~spl11_2 | ~spl11_3 | ~spl11_4 | spl11_5 | ~spl11_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f182,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    v3_orders_2(sK0) | ~spl11_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl11_2 <=> v3_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ~v3_orders_2(sK0) | (~spl11_3 | ~spl11_4 | spl11_5 | ~spl11_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f181,f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl11_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    spl11_7 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | (~spl11_3 | ~spl11_4 | spl11_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f180,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ~r1_orders_2(sK0,sK1,sK1) | spl11_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl11_5 <=> r1_orders_2(sK0,sK1,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    r1_orders_2(sK0,sK1,sK1) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | (~spl11_3 | ~spl11_4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f178,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    l1_orders_2(sK0) | ~spl11_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl11_3 <=> l1_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ~l1_orders_2(sK0) | r1_orders_2(sK0,sK1,sK1) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~spl11_4),
% 0.22/0.49    inference(resolution,[],[f172,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl11_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl11_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_orders_2(X1,X0,X0) | ~r2_hidden(X0,u1_struct_0(X1)) | ~v3_orders_2(X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f171,f135])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_orders_2(X0) | v1_relat_1(u1_orders_2(X0))) )),
% 0.22/0.49    inference(resolution,[],[f134,f109])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))) | ~l1_orders_2(X0) | v1_relat_1(u1_orders_2(X0))) )),
% 0.22/0.49    inference(resolution,[],[f36,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    ( ! [X4,X5] : (v1_relat_1(k2_zfmisc_1(X4,X5))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f131,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ( ! [X4,X5] : (sK3(k2_zfmisc_1(X4,X5)) = k4_tarski(sK7(X4,X5,sK3(k2_zfmisc_1(X4,X5))),sK8(X4,X5,sK3(k2_zfmisc_1(X4,X5)))) | v1_relat_1(k2_zfmisc_1(X4,X5))) )),
% 0.22/0.49    inference(resolution,[],[f56,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3) )),
% 0.22/0.49    inference(equality_resolution,[],[f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k4_tarski(sK7(X0,X1,X3),sK8(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_orders_2(X1,X0,X0) | ~r2_hidden(X0,u1_struct_0(X1)) | ~v1_relat_1(u1_orders_2(X1)) | ~v3_orders_2(X1)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f168])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_orders_2(X1,X0,X0) | ~r2_hidden(X0,u1_struct_0(X1)) | ~v1_relat_1(u1_orders_2(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1)) )),
% 0.22/0.49    inference(resolution,[],[f39,f124])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X0),u1_orders_2(X1)) | ~r2_hidden(X0,u1_struct_0(X1)) | ~v1_relat_1(u1_orders_2(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1)) )),
% 0.22/0.49    inference(resolution,[],[f32,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0] : (r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : ((v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (l1_orders_2(X0) => (v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_orders_2)).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_relat_2(X0,X1) | ~r2_hidden(X2,X1) | r2_hidden(k4_tarski(X2,X2),X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k4_tarski(X2,X2),X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    ~spl11_2 | ~spl11_3 | ~spl11_4 | spl11_5 | ~spl11_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    $false | (~spl11_2 | ~spl11_3 | ~spl11_4 | spl11_5 | ~spl11_7)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f67,f72,f94,f82,f77,f172])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    spl11_11 | ~spl11_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f136,f70,f138])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl11_11 <=> v1_relat_1(u1_orders_2(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.22/0.49  % (28767)Refutation not found, incomplete strategy% (28767)------------------------------
% 0.22/0.49  % (28767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28767)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (28767)Memory used [KB]: 10618
% 0.22/0.49  % (28767)Time elapsed: 0.073 s
% 0.22/0.49  % (28767)------------------------------
% 0.22/0.49  % (28767)------------------------------
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    v1_relat_1(u1_orders_2(sK0)) | ~spl11_3),
% 0.22/0.49    inference(resolution,[],[f135,f72])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    ~spl11_9 | spl11_10 | ~spl11_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f111,f92,f120,f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    spl11_9 <=> v1_relat_1(u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    spl11_10 <=> sK1 = k4_tarski(sK4(sK1),sK5(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    sK1 = k4_tarski(sK4(sK1),sK5(sK1)) | ~v1_relat_1(u1_struct_0(sK0)) | ~spl11_7),
% 0.22/0.49    inference(resolution,[],[f42,f94])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_tarski(sK4(X1),sK5(X1)) = X1 | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl11_1 | ~spl11_6 | ~spl11_8),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    $false | (spl11_1 | ~spl11_6 | ~spl11_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f103,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~v2_struct_0(sK0) | spl11_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl11_1 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    v2_struct_0(sK0) | (~spl11_6 | ~spl11_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f101,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    l1_struct_0(sK0) | ~spl11_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl11_6 <=> l1_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl11_8),
% 0.22/0.49    inference(resolution,[],[f98,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    v1_xboole_0(u1_struct_0(sK0)) | ~spl11_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    spl11_8 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl11_1 | ~spl11_6 | ~spl11_8),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f100])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    $false | (spl11_1 | ~spl11_6 | ~spl11_8)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f62,f88,f98,f41])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl11_7 | spl11_8 | ~spl11_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f90,f75,f96,f92])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0)) | ~spl11_4),
% 0.22/0.49    inference(resolution,[],[f45,f77])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl11_6 | ~spl11_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f84,f70,f86])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    l1_struct_0(sK0) | ~spl11_3),
% 0.22/0.49    inference(resolution,[],[f35,f72])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ~spl11_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f80])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ~r1_orders_2(sK0,sK1,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (~r1_orders_2(X0,X1,X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (~r1_orders_2(X0,X1,X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.22/0.49    inference(negated_conjecture,[],[f11])).
% 0.22/0.49  fof(f11,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl11_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f75])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl11_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f70])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    l1_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl11_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f65])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v3_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~spl11_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f60])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (28755)------------------------------
% 0.22/0.49  % (28755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28755)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (28755)Memory used [KB]: 6268
% 0.22/0.49  % (28755)Time elapsed: 0.071 s
% 0.22/0.49  % (28755)------------------------------
% 0.22/0.49  % (28755)------------------------------
% 0.22/0.49  % (28746)Success in time 0.129 s
%------------------------------------------------------------------------------
