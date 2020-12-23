%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:24 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 188 expanded)
%              Number of leaves         :   33 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  349 ( 505 expanded)
%              Number of equality atoms :   40 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f322,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f105,f110,f115,f122,f129,f141,f146,f156,f174,f214,f215,f251,f284,f321])).

fof(f321,plain,
    ( ~ spl5_7
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f319,f279])).

fof(f279,plain,
    ( ! [X2] : k1_xboole_0 != k1_tarski(X2)
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f278,f186])).

fof(f186,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)
    | ~ spl5_11 ),
    inference(resolution,[],[f167,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f167,plain,
    ( ! [X1] : r1_xboole_0(k1_xboole_0,X1)
    | ~ spl5_11 ),
    inference(resolution,[],[f160,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f160,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_11 ),
    inference(resolution,[],[f155,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f155,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl5_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f278,plain,
    ( ! [X2] : k1_tarski(X2) != k3_xboole_0(k1_xboole_0,k1_tarski(X2))
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f134,f145])).

fof(f145,plain,
    ( k1_xboole_0 = sK2(sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl5_10
  <=> k1_xboole_0 = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f134,plain,
    ( ! [X2] : k1_tarski(X2) != k3_xboole_0(sK2(sK0),k1_tarski(X2))
    | ~ spl5_7 ),
    inference(resolution,[],[f123,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f123,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f121,f59])).

fof(f121,plain,
    ( v1_xboole_0(sK2(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_7
  <=> v1_xboole_0(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f319,plain,
    ( k1_xboole_0 = k1_tarski(k2_struct_0(sK0))
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f318,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f318,plain,
    ( ~ r1_tarski(k1_tarski(k2_struct_0(sK0)),k1_tarski(k2_struct_0(sK0)))
    | k1_xboole_0 = k1_tarski(k2_struct_0(sK0))
    | ~ spl5_24 ),
    inference(resolution,[],[f285,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f285,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tarski(k2_struct_0(sK0)))
        | k1_xboole_0 = X0 )
    | ~ spl5_24 ),
    inference(resolution,[],[f283,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f283,plain,
    ( r1_xboole_0(k1_tarski(k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl5_24
  <=> r1_xboole_0(k1_tarski(k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f284,plain,
    ( spl5_24
    | spl5_20 ),
    inference(avatar_split_clause,[],[f255,f248,f281])).

fof(f248,plain,
    ( spl5_20
  <=> r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f255,plain,
    ( r1_xboole_0(k1_tarski(k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_20 ),
    inference(resolution,[],[f250,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f250,plain,
    ( ~ r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f248])).

fof(f251,plain,
    ( ~ spl5_20
    | spl5_16 ),
    inference(avatar_split_clause,[],[f218,f211,f248])).

fof(f211,plain,
    ( spl5_16
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f218,plain,
    ( ~ r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_16 ),
    inference(resolution,[],[f213,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f213,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f211])).

fof(f215,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | r1_tarski(sK1,k2_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f214,plain,
    ( ~ spl5_15
    | ~ spl5_16
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f204,f171,f138,f112,f102,f92,f87,f211,f207])).

% (15464)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f207,plain,
    ( spl5_15
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f87,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f92,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f102,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f112,plain,
    ( spl5_6
  <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f138,plain,
    ( spl5_9
  <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f171,plain,
    ( spl5_12
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f204,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f159,f173])).

fof(f173,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f159,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f158,f140])).

fof(f140,plain,
    ( k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f158,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6 ),
    inference(subsumption_resolution,[],[f157,f104])).

fof(f104,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f157,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_6 ),
    inference(resolution,[],[f151,f114])).

fof(f114,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( m2_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f96,f94])).

fof(f94,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f89,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f89,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f174,plain,
    ( spl5_12
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f117,f107,f171])).

fof(f107,plain,
    ( spl5_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f117,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f109,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f109,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f156,plain,
    ( spl5_11
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f148,f143,f119,f153])).

fof(f148,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(superposition,[],[f121,f145])).

fof(f146,plain,
    ( spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f124,f119,f143])).

fof(f124,plain,
    ( k1_xboole_0 = sK2(sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f121,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f141,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f136,f92,f87,f138])).

fof(f136,plain,
    ( k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f98,f94])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f89,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f129,plain,
    ( spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f116,f102,f126])).

fof(f126,plain,
    ( spl5_8
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f116,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f104,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f122,plain,
    ( spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f99,f92,f119])).

fof(f99,plain,
    ( v1_xboole_0(sK2(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f94,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v1_xboole_0(sK2(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_connsp_1)).

fof(f115,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f45,f112])).

fof(f45,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f110,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f100,f92,f107])).

fof(f100,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f94,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f105,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f44,f102])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f48,f92])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f47,f87])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:09:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (15458)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (15457)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15461)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (15450)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (15459)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.53  % (15451)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.53  % (15446)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (15462)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.42/0.56  % (15453)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.42/0.57  % (15445)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.42/0.58  % (15448)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.42/0.58  % (15463)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.42/0.58  % (15460)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.65/0.58  % (15447)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.65/0.58  % (15455)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.65/0.59  % (15452)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.65/0.59  % (15448)Refutation found. Thanks to Tanya!
% 1.65/0.59  % SZS status Theorem for theBenchmark
% 1.65/0.59  % SZS output start Proof for theBenchmark
% 1.65/0.59  fof(f322,plain,(
% 1.65/0.59    $false),
% 1.65/0.59    inference(avatar_sat_refutation,[],[f90,f95,f105,f110,f115,f122,f129,f141,f146,f156,f174,f214,f215,f251,f284,f321])).
% 1.65/0.59  fof(f321,plain,(
% 1.65/0.59    ~spl5_7 | ~spl5_10 | ~spl5_11 | ~spl5_24),
% 1.65/0.59    inference(avatar_contradiction_clause,[],[f320])).
% 1.65/0.59  fof(f320,plain,(
% 1.65/0.59    $false | (~spl5_7 | ~spl5_10 | ~spl5_11 | ~spl5_24)),
% 1.65/0.59    inference(subsumption_resolution,[],[f319,f279])).
% 1.65/0.59  fof(f279,plain,(
% 1.65/0.59    ( ! [X2] : (k1_xboole_0 != k1_tarski(X2)) ) | (~spl5_7 | ~spl5_10 | ~spl5_11)),
% 1.65/0.59    inference(forward_demodulation,[],[f278,f186])).
% 1.65/0.59  fof(f186,plain,(
% 1.65/0.59    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) ) | ~spl5_11),
% 1.65/0.59    inference(resolution,[],[f167,f70])).
% 1.65/0.59  fof(f70,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.65/0.59    inference(cnf_transformation,[],[f3])).
% 1.65/0.59  fof(f3,axiom,(
% 1.65/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.65/0.59  fof(f167,plain,(
% 1.65/0.59    ( ! [X1] : (r1_xboole_0(k1_xboole_0,X1)) ) | ~spl5_11),
% 1.65/0.59    inference(resolution,[],[f160,f63])).
% 1.65/0.59  fof(f63,plain,(
% 1.65/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f35])).
% 1.65/0.59  fof(f35,plain,(
% 1.65/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.65/0.59    inference(ennf_transformation,[],[f24])).
% 1.65/0.59  fof(f24,plain,(
% 1.65/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.59    inference(rectify,[],[f4])).
% 1.65/0.59  fof(f4,axiom,(
% 1.65/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.65/0.59  fof(f160,plain,(
% 1.65/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_11),
% 1.65/0.59    inference(resolution,[],[f155,f59])).
% 1.65/0.59  fof(f59,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f2])).
% 1.65/0.59  fof(f2,axiom,(
% 1.65/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.65/0.59  fof(f155,plain,(
% 1.65/0.59    v1_xboole_0(k1_xboole_0) | ~spl5_11),
% 1.65/0.59    inference(avatar_component_clause,[],[f153])).
% 1.65/0.59  fof(f153,plain,(
% 1.65/0.59    spl5_11 <=> v1_xboole_0(k1_xboole_0)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.65/0.59  fof(f278,plain,(
% 1.65/0.59    ( ! [X2] : (k1_tarski(X2) != k3_xboole_0(k1_xboole_0,k1_tarski(X2))) ) | (~spl5_7 | ~spl5_10)),
% 1.65/0.59    inference(forward_demodulation,[],[f134,f145])).
% 1.65/0.59  fof(f145,plain,(
% 1.65/0.59    k1_xboole_0 = sK2(sK0) | ~spl5_10),
% 1.65/0.59    inference(avatar_component_clause,[],[f143])).
% 1.65/0.59  fof(f143,plain,(
% 1.65/0.59    spl5_10 <=> k1_xboole_0 = sK2(sK0)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.65/0.59  fof(f134,plain,(
% 1.65/0.59    ( ! [X2] : (k1_tarski(X2) != k3_xboole_0(sK2(sK0),k1_tarski(X2))) ) | ~spl5_7),
% 1.65/0.59    inference(resolution,[],[f123,f68])).
% 1.65/0.59  fof(f68,plain,(
% 1.65/0.59    ( ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f39])).
% 1.65/0.59  fof(f39,plain,(
% 1.65/0.59    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 1.65/0.59    inference(ennf_transformation,[],[f11])).
% 1.65/0.59  fof(f11,axiom,(
% 1.65/0.59    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).
% 1.65/0.59  fof(f123,plain,(
% 1.65/0.59    ( ! [X0] : (~r2_hidden(X0,sK2(sK0))) ) | ~spl5_7),
% 1.65/0.59    inference(resolution,[],[f121,f59])).
% 1.65/0.59  fof(f121,plain,(
% 1.65/0.59    v1_xboole_0(sK2(sK0)) | ~spl5_7),
% 1.65/0.59    inference(avatar_component_clause,[],[f119])).
% 1.65/0.59  fof(f119,plain,(
% 1.65/0.59    spl5_7 <=> v1_xboole_0(sK2(sK0))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.65/0.59  fof(f319,plain,(
% 1.65/0.59    k1_xboole_0 = k1_tarski(k2_struct_0(sK0)) | ~spl5_24),
% 1.65/0.59    inference(subsumption_resolution,[],[f318,f79])).
% 1.65/0.59  fof(f79,plain,(
% 1.65/0.59    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 1.65/0.59    inference(equality_resolution,[],[f73])).
% 1.65/0.59  fof(f73,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f10])).
% 1.65/0.59  fof(f10,axiom,(
% 1.65/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.65/0.59  fof(f318,plain,(
% 1.65/0.59    ~r1_tarski(k1_tarski(k2_struct_0(sK0)),k1_tarski(k2_struct_0(sK0))) | k1_xboole_0 = k1_tarski(k2_struct_0(sK0)) | ~spl5_24),
% 1.65/0.59    inference(resolution,[],[f285,f49])).
% 1.65/0.59  fof(f49,plain,(
% 1.65/0.59    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f12])).
% 1.65/0.59  fof(f12,axiom,(
% 1.65/0.59    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 1.65/0.59  fof(f285,plain,(
% 1.65/0.59    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tarski(k2_struct_0(sK0))) | k1_xboole_0 = X0) ) | ~spl5_24),
% 1.65/0.59    inference(resolution,[],[f283,f78])).
% 1.65/0.59  fof(f78,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0) )),
% 1.65/0.59    inference(cnf_transformation,[],[f43])).
% 1.65/0.59  fof(f43,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.65/0.59    inference(flattening,[],[f42])).
% 1.65/0.59  fof(f42,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.65/0.59    inference(ennf_transformation,[],[f7])).
% 1.65/0.59  fof(f7,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 1.65/0.59  fof(f283,plain,(
% 1.65/0.59    r1_xboole_0(k1_tarski(k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_24),
% 1.65/0.59    inference(avatar_component_clause,[],[f281])).
% 1.65/0.59  fof(f281,plain,(
% 1.65/0.59    spl5_24 <=> r1_xboole_0(k1_tarski(k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.65/0.59  fof(f284,plain,(
% 1.65/0.59    spl5_24 | spl5_20),
% 1.65/0.59    inference(avatar_split_clause,[],[f255,f248,f281])).
% 1.65/0.59  fof(f248,plain,(
% 1.65/0.59    spl5_20 <=> r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.65/0.59  fof(f255,plain,(
% 1.65/0.59    r1_xboole_0(k1_tarski(k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) | spl5_20),
% 1.65/0.59    inference(resolution,[],[f250,f65])).
% 1.65/0.59  fof(f65,plain,(
% 1.65/0.59    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f36])).
% 1.65/0.59  fof(f36,plain,(
% 1.65/0.59    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.65/0.59    inference(ennf_transformation,[],[f9])).
% 1.65/0.59  fof(f9,axiom,(
% 1.65/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.65/0.59  fof(f250,plain,(
% 1.65/0.59    ~r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl5_20),
% 1.65/0.59    inference(avatar_component_clause,[],[f248])).
% 1.65/0.59  fof(f251,plain,(
% 1.65/0.59    ~spl5_20 | spl5_16),
% 1.65/0.59    inference(avatar_split_clause,[],[f218,f211,f248])).
% 1.65/0.59  fof(f211,plain,(
% 1.65/0.59    spl5_16 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.65/0.59  fof(f218,plain,(
% 1.65/0.59    ~r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl5_16),
% 1.65/0.59    inference(resolution,[],[f213,f67])).
% 1.65/0.59  fof(f67,plain,(
% 1.65/0.59    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f38])).
% 1.65/0.59  fof(f38,plain,(
% 1.65/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.65/0.59    inference(ennf_transformation,[],[f15])).
% 1.65/0.59  fof(f15,axiom,(
% 1.65/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.65/0.59  fof(f213,plain,(
% 1.65/0.59    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl5_16),
% 1.65/0.59    inference(avatar_component_clause,[],[f211])).
% 1.65/0.59  fof(f215,plain,(
% 1.65/0.59    u1_struct_0(sK0) != k2_struct_0(sK0) | r1_tarski(sK1,k2_struct_0(sK0)) | ~r1_tarski(sK1,u1_struct_0(sK0))),
% 1.65/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.65/0.59  fof(f214,plain,(
% 1.65/0.59    ~spl5_15 | ~spl5_16 | ~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_9 | ~spl5_12),
% 1.65/0.59    inference(avatar_split_clause,[],[f204,f171,f138,f112,f102,f92,f87,f211,f207])).
% 1.65/0.59  % (15464)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.65/0.59  fof(f207,plain,(
% 1.65/0.59    spl5_15 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.65/0.59  fof(f87,plain,(
% 1.65/0.59    spl5_2 <=> v2_pre_topc(sK0)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.65/0.59  fof(f92,plain,(
% 1.65/0.59    spl5_3 <=> l1_pre_topc(sK0)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.65/0.59  fof(f102,plain,(
% 1.65/0.59    spl5_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.65/0.59  fof(f112,plain,(
% 1.65/0.59    spl5_6 <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.65/0.59  fof(f138,plain,(
% 1.65/0.59    spl5_9 <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.65/0.59  fof(f171,plain,(
% 1.65/0.59    spl5_12 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.65/0.59  fof(f204,plain,(
% 1.65/0.59    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK1,k2_struct_0(sK0)) | (~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_9 | ~spl5_12)),
% 1.65/0.59    inference(forward_demodulation,[],[f159,f173])).
% 1.65/0.59  fof(f173,plain,(
% 1.65/0.59    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl5_12),
% 1.65/0.59    inference(avatar_component_clause,[],[f171])).
% 1.65/0.59  fof(f159,plain,(
% 1.65/0.59    ~r1_tarski(sK1,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_6 | ~spl5_9)),
% 1.65/0.59    inference(forward_demodulation,[],[f158,f140])).
% 1.65/0.59  fof(f140,plain,(
% 1.65/0.59    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | ~spl5_9),
% 1.65/0.59    inference(avatar_component_clause,[],[f138])).
% 1.65/0.59  fof(f158,plain,(
% 1.65/0.59    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_6)),
% 1.65/0.59    inference(subsumption_resolution,[],[f157,f104])).
% 1.65/0.59  fof(f104,plain,(
% 1.65/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_4),
% 1.65/0.59    inference(avatar_component_clause,[],[f102])).
% 1.65/0.59  fof(f157,plain,(
% 1.65/0.59    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_2 | ~spl5_3 | spl5_6)),
% 1.65/0.59    inference(resolution,[],[f151,f114])).
% 1.65/0.59  fof(f114,plain,(
% 1.65/0.59    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | spl5_6),
% 1.65/0.59    inference(avatar_component_clause,[],[f112])).
% 1.65/0.59  fof(f151,plain,(
% 1.65/0.59    ( ! [X0,X1] : (m2_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_3)),
% 1.65/0.59    inference(subsumption_resolution,[],[f96,f94])).
% 1.65/0.59  fof(f94,plain,(
% 1.65/0.59    l1_pre_topc(sK0) | ~spl5_3),
% 1.65/0.59    inference(avatar_component_clause,[],[f92])).
% 1.65/0.59  fof(f96,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0)) ) | ~spl5_2),
% 1.65/0.59    inference(resolution,[],[f89,f56])).
% 1.65/0.59  fof(f56,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f34])).
% 1.65/0.59  fof(f34,plain,(
% 1.65/0.59    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/0.59    inference(flattening,[],[f33])).
% 1.65/0.59  fof(f33,plain,(
% 1.65/0.59    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.65/0.59    inference(ennf_transformation,[],[f20])).
% 1.65/0.59  fof(f20,axiom,(
% 1.65/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 1.65/0.59  fof(f89,plain,(
% 1.65/0.59    v2_pre_topc(sK0) | ~spl5_2),
% 1.65/0.59    inference(avatar_component_clause,[],[f87])).
% 1.65/0.59  fof(f174,plain,(
% 1.65/0.59    spl5_12 | ~spl5_5),
% 1.65/0.59    inference(avatar_split_clause,[],[f117,f107,f171])).
% 1.65/0.59  fof(f107,plain,(
% 1.65/0.59    spl5_5 <=> l1_struct_0(sK0)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.65/0.59  fof(f117,plain,(
% 1.65/0.59    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl5_5),
% 1.65/0.59    inference(resolution,[],[f109,f50])).
% 1.65/0.59  fof(f50,plain,(
% 1.65/0.59    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f27])).
% 1.65/0.59  fof(f27,plain,(
% 1.65/0.59    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f17])).
% 1.65/0.59  fof(f17,axiom,(
% 1.65/0.59    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.65/0.59  fof(f109,plain,(
% 1.65/0.59    l1_struct_0(sK0) | ~spl5_5),
% 1.65/0.59    inference(avatar_component_clause,[],[f107])).
% 1.65/0.59  fof(f156,plain,(
% 1.65/0.59    spl5_11 | ~spl5_7 | ~spl5_10),
% 1.65/0.59    inference(avatar_split_clause,[],[f148,f143,f119,f153])).
% 1.65/0.59  fof(f148,plain,(
% 1.65/0.59    v1_xboole_0(k1_xboole_0) | (~spl5_7 | ~spl5_10)),
% 1.65/0.59    inference(superposition,[],[f121,f145])).
% 1.65/0.59  fof(f146,plain,(
% 1.65/0.59    spl5_10 | ~spl5_7),
% 1.65/0.59    inference(avatar_split_clause,[],[f124,f119,f143])).
% 1.65/0.59  fof(f124,plain,(
% 1.65/0.59    k1_xboole_0 = sK2(sK0) | ~spl5_7),
% 1.65/0.59    inference(resolution,[],[f121,f51])).
% 1.65/0.59  fof(f51,plain,(
% 1.65/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.65/0.59    inference(cnf_transformation,[],[f28])).
% 1.65/0.59  fof(f28,plain,(
% 1.65/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f8])).
% 1.65/0.59  fof(f8,axiom,(
% 1.65/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).
% 1.65/0.59  fof(f141,plain,(
% 1.65/0.59    spl5_9 | ~spl5_2 | ~spl5_3),
% 1.65/0.59    inference(avatar_split_clause,[],[f136,f92,f87,f138])).
% 1.65/0.59  fof(f136,plain,(
% 1.65/0.59    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | (~spl5_2 | ~spl5_3)),
% 1.65/0.59    inference(subsumption_resolution,[],[f98,f94])).
% 1.65/0.59  fof(f98,plain,(
% 1.65/0.59    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | ~spl5_2),
% 1.65/0.59    inference(resolution,[],[f89,f55])).
% 1.65/0.59  fof(f55,plain,(
% 1.65/0.59    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f32])).
% 1.65/0.59  fof(f32,plain,(
% 1.65/0.59    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/0.59    inference(flattening,[],[f31])).
% 1.65/0.59  fof(f31,plain,(
% 1.65/0.59    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.65/0.59    inference(ennf_transformation,[],[f19])).
% 1.65/0.59  fof(f19,axiom,(
% 1.65/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 1.65/0.59  fof(f129,plain,(
% 1.65/0.59    spl5_8 | ~spl5_4),
% 1.65/0.59    inference(avatar_split_clause,[],[f116,f102,f126])).
% 1.65/0.59  fof(f126,plain,(
% 1.65/0.59    spl5_8 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.65/0.59  fof(f116,plain,(
% 1.65/0.59    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_4),
% 1.65/0.59    inference(resolution,[],[f104,f75])).
% 1.65/0.59  fof(f75,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f16])).
% 1.65/0.59  fof(f16,axiom,(
% 1.65/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.65/0.59  fof(f122,plain,(
% 1.65/0.59    spl5_7 | ~spl5_3),
% 1.65/0.59    inference(avatar_split_clause,[],[f99,f92,f119])).
% 1.65/0.59  fof(f99,plain,(
% 1.65/0.59    v1_xboole_0(sK2(sK0)) | ~spl5_3),
% 1.65/0.59    inference(resolution,[],[f94,f54])).
% 1.65/0.59  fof(f54,plain,(
% 1.65/0.59    ( ! [X0] : (~l1_pre_topc(X0) | v1_xboole_0(sK2(X0))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f30])).
% 1.65/0.59  fof(f30,plain,(
% 1.65/0.59    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f21])).
% 1.65/0.59  fof(f21,axiom,(
% 1.65/0.59    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_connsp_1)).
% 1.65/0.59  fof(f115,plain,(
% 1.65/0.59    ~spl5_6),
% 1.65/0.59    inference(avatar_split_clause,[],[f45,f112])).
% 1.65/0.59  fof(f45,plain,(
% 1.65/0.59    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 1.65/0.59    inference(cnf_transformation,[],[f26])).
% 1.65/0.59  fof(f26,plain,(
% 1.65/0.59    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.65/0.59    inference(flattening,[],[f25])).
% 1.65/0.59  fof(f25,plain,(
% 1.65/0.59    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.65/0.59    inference(ennf_transformation,[],[f23])).
% 1.65/0.59  fof(f23,negated_conjecture,(
% 1.65/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.65/0.59    inference(negated_conjecture,[],[f22])).
% 1.65/0.59  fof(f22,conjecture,(
% 1.65/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 1.65/0.59  fof(f110,plain,(
% 1.65/0.59    spl5_5 | ~spl5_3),
% 1.65/0.59    inference(avatar_split_clause,[],[f100,f92,f107])).
% 1.65/0.59  fof(f100,plain,(
% 1.65/0.59    l1_struct_0(sK0) | ~spl5_3),
% 1.65/0.59    inference(resolution,[],[f94,f52])).
% 1.65/0.59  fof(f52,plain,(
% 1.65/0.59    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f29])).
% 1.65/0.59  fof(f29,plain,(
% 1.65/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f18])).
% 1.65/0.59  fof(f18,axiom,(
% 1.65/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.65/0.59  fof(f105,plain,(
% 1.65/0.59    spl5_4),
% 1.65/0.59    inference(avatar_split_clause,[],[f44,f102])).
% 1.65/0.59  fof(f44,plain,(
% 1.65/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.59    inference(cnf_transformation,[],[f26])).
% 1.65/0.59  fof(f95,plain,(
% 1.65/0.59    spl5_3),
% 1.65/0.59    inference(avatar_split_clause,[],[f48,f92])).
% 1.65/0.59  fof(f48,plain,(
% 1.65/0.59    l1_pre_topc(sK0)),
% 1.65/0.59    inference(cnf_transformation,[],[f26])).
% 1.65/0.59  fof(f90,plain,(
% 1.65/0.59    spl5_2),
% 1.65/0.59    inference(avatar_split_clause,[],[f47,f87])).
% 1.65/0.59  fof(f47,plain,(
% 1.65/0.59    v2_pre_topc(sK0)),
% 1.65/0.59    inference(cnf_transformation,[],[f26])).
% 1.65/0.59  % SZS output end Proof for theBenchmark
% 1.65/0.59  % (15448)------------------------------
% 1.65/0.59  % (15448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (15448)Termination reason: Refutation
% 1.65/0.59  
% 1.65/0.59  % (15448)Memory used [KB]: 10746
% 1.65/0.59  % (15448)Time elapsed: 0.138 s
% 1.65/0.59  % (15448)------------------------------
% 1.65/0.59  % (15448)------------------------------
% 1.65/0.59  % (15444)Success in time 0.219 s
%------------------------------------------------------------------------------
