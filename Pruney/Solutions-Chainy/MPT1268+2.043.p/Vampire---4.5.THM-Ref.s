%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 206 expanded)
%              Number of leaves         :   17 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  270 (1021 expanded)
%              Number of equality atoms :   27 ( 115 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f459,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f90,f95,f116,f144,f228,f458])).

fof(f458,plain,
    ( spl5_1
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f456])).

fof(f456,plain,
    ( $false
    | spl5_1
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f80,f375,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f375,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f59,f58,f249,f143])).

fof(f143,plain,
    ( ! [X2] :
        ( ~ v3_pre_topc(X2,sK0)
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_6
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f249,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f36,f34,f70,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f70,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f35,f36,f34,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f36,f34,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f80,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f60,f59,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f60,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f34,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f228,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f94,f200,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f200,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f181,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f181,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f42,f174,f44])).

fof(f174,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f172,f166])).

fof(f166,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f35,f36,f36,f89,f115,f115,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f115,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f89,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_3
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f172,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f168,f145])).

fof(f145,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f36,f34,f69,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f168,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f36,f74,f34,f115,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f74,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f94,plain,
    ( k1_xboole_0 != sK2
    | spl5_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f144,plain,
    ( spl5_1
    | spl5_6 ),
    inference(avatar_split_clause,[],[f33,f142,f68])).

fof(f33,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f116,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f29,f113,f68])).

fof(f29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,
    ( ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f32,f92,f68])).

fof(f32,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f31,f87,f68])).

fof(f31,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f30,f72,f68])).

fof(f30,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:44:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.53  % (28111)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (28102)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (28095)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (28094)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (28093)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.56  % (28118)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (28110)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.57  % (28093)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (28106)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.57  % (28101)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f459,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(avatar_sat_refutation,[],[f75,f90,f95,f116,f144,f228,f458])).
% 0.20/0.59  fof(f458,plain,(
% 0.20/0.59    spl5_1 | ~spl5_6),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f456])).
% 0.20/0.59  fof(f456,plain,(
% 0.20/0.59    $false | (spl5_1 | ~spl5_6)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f80,f375,f45])).
% 0.20/0.59  fof(f45,plain,(
% 0.20/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.59  fof(f375,plain,(
% 0.20/0.59    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_6)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f59,f58,f249,f143])).
% 0.20/0.59  fof(f143,plain,(
% 0.20/0.59    ( ! [X2] : (~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1)) ) | ~spl5_6),
% 0.20/0.59    inference(avatar_component_clause,[],[f142])).
% 0.20/0.59  fof(f142,plain,(
% 0.20/0.59    spl5_6 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.59  fof(f249,plain,(
% 0.20/0.59    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl5_1),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f36,f34,f70,f40])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tops_1(X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f19,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f11])).
% 0.20/0.59  fof(f11,axiom,(
% 0.20/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.59  fof(f70,plain,(
% 0.20/0.59    ~v2_tops_1(sK1,sK0) | spl5_1),
% 0.20/0.59    inference(avatar_component_clause,[],[f68])).
% 0.20/0.59  fof(f68,plain,(
% 0.20/0.59    spl5_1 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.59  fof(f34,plain,(
% 0.20/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  fof(f15,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f14])).
% 0.20/0.59  fof(f14,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f13])).
% 0.20/0.59  fof(f13,negated_conjecture,(
% 0.20/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.59    inference(negated_conjecture,[],[f12])).
% 0.20/0.59  fof(f12,conjecture,(
% 0.20/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.20/0.59  fof(f36,plain,(
% 0.20/0.59    l1_pre_topc(sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  fof(f58,plain,(
% 0.20/0.59    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f35,f36,f34,f43])).
% 0.20/0.59  fof(f43,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f21])).
% 0.20/0.59  fof(f21,plain,(
% 0.20/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f20])).
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f7])).
% 0.20/0.59  fof(f7,axiom,(
% 0.20/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    v2_pre_topc(sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  fof(f59,plain,(
% 0.20/0.59    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f36,f34,f48])).
% 0.20/0.59  fof(f48,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f26])).
% 0.20/0.59  fof(f26,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,axiom,(
% 0.20/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.59  fof(f80,plain,(
% 0.20/0.59    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f60,f59,f44])).
% 0.20/0.59  fof(f44,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f23])).
% 0.20/0.59  fof(f23,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.59    inference(flattening,[],[f22])).
% 0.20/0.59  fof(f22,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.59    inference(ennf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.59  fof(f60,plain,(
% 0.20/0.59    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f34,f46])).
% 0.20/0.59  fof(f46,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f5])).
% 0.20/0.59  fof(f228,plain,(
% 0.20/0.59    ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f222])).
% 0.20/0.59  fof(f222,plain,(
% 0.20/0.59    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f94,f200,f37])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f16])).
% 0.20/0.59  fof(f16,plain,(
% 0.20/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.59    inference(ennf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.59  fof(f200,plain,(
% 0.20/0.59    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f181,f49])).
% 0.20/0.59  fof(f49,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f27])).
% 0.20/0.59  fof(f27,plain,(
% 0.20/0.59    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,axiom,(
% 0.20/0.59    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.59  fof(f181,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(sK2,X0)) ) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f42,f174,f44])).
% 0.20/0.59  fof(f174,plain,(
% 0.20/0.59    r1_tarski(sK2,k1_xboole_0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.20/0.59    inference(backward_demodulation,[],[f172,f166])).
% 0.20/0.59  fof(f166,plain,(
% 0.20/0.59    sK2 = k1_tops_1(sK0,sK2) | (~spl5_3 | ~spl5_5)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f35,f36,f36,f89,f115,f115,f39])).
% 0.20/0.59  fof(f39,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f17])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f10])).
% 0.20/0.59  fof(f10,axiom,(
% 0.20/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.20/0.59  fof(f115,plain,(
% 0.20/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.20/0.59    inference(avatar_component_clause,[],[f113])).
% 0.20/0.59  fof(f113,plain,(
% 0.20/0.59    spl5_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.59  fof(f89,plain,(
% 0.20/0.59    v3_pre_topc(sK2,sK0) | ~spl5_3),
% 0.20/0.59    inference(avatar_component_clause,[],[f87])).
% 0.20/0.59  fof(f87,plain,(
% 0.20/0.59    spl5_3 <=> v3_pre_topc(sK2,sK0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.59  fof(f172,plain,(
% 0.20/0.59    r1_tarski(k1_tops_1(sK0,sK2),k1_xboole_0) | (~spl5_1 | ~spl5_2 | ~spl5_5)),
% 0.20/0.59    inference(forward_demodulation,[],[f168,f145])).
% 0.20/0.59  fof(f145,plain,(
% 0.20/0.59    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl5_1),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f36,f34,f69,f41])).
% 0.20/0.59  fof(f41,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    v2_tops_1(sK1,sK0) | ~spl5_1),
% 0.20/0.59    inference(avatar_component_clause,[],[f68])).
% 0.20/0.59  fof(f168,plain,(
% 0.20/0.59    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) | (~spl5_2 | ~spl5_5)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f36,f74,f34,f115,f47])).
% 0.20/0.59  fof(f47,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f25])).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f24])).
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f9])).
% 0.20/0.59  fof(f9,axiom,(
% 0.20/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.20/0.59  fof(f74,plain,(
% 0.20/0.59    r1_tarski(sK2,sK1) | ~spl5_2),
% 0.20/0.59    inference(avatar_component_clause,[],[f72])).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    spl5_2 <=> r1_tarski(sK2,sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.59  fof(f42,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.59  fof(f94,plain,(
% 0.20/0.59    k1_xboole_0 != sK2 | spl5_4),
% 0.20/0.59    inference(avatar_component_clause,[],[f92])).
% 0.20/0.59  fof(f92,plain,(
% 0.20/0.59    spl5_4 <=> k1_xboole_0 = sK2),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.59  fof(f144,plain,(
% 0.20/0.59    spl5_1 | spl5_6),
% 0.20/0.59    inference(avatar_split_clause,[],[f33,f142,f68])).
% 0.20/0.59  fof(f33,plain,(
% 0.20/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | ~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | v2_tops_1(sK1,sK0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  fof(f116,plain,(
% 0.20/0.59    ~spl5_1 | spl5_5),
% 0.20/0.59    inference(avatar_split_clause,[],[f29,f113,f68])).
% 0.20/0.59  fof(f29,plain,(
% 0.20/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  fof(f95,plain,(
% 0.20/0.59    ~spl5_1 | ~spl5_4),
% 0.20/0.59    inference(avatar_split_clause,[],[f32,f92,f68])).
% 0.20/0.59  fof(f32,plain,(
% 0.20/0.59    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  fof(f90,plain,(
% 0.20/0.59    ~spl5_1 | spl5_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f31,f87,f68])).
% 0.20/0.59  fof(f31,plain,(
% 0.20/0.59    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  fof(f75,plain,(
% 0.20/0.59    ~spl5_1 | spl5_2),
% 0.20/0.59    inference(avatar_split_clause,[],[f30,f72,f68])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (28093)------------------------------
% 0.20/0.59  % (28093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (28093)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (28093)Memory used [KB]: 6396
% 0.20/0.59  % (28093)Time elapsed: 0.143 s
% 0.20/0.59  % (28093)------------------------------
% 0.20/0.59  % (28093)------------------------------
% 0.20/0.60  % (28086)Success in time 0.24 s
%------------------------------------------------------------------------------
