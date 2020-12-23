%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:07 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 727 expanded)
%              Number of leaves         :   21 ( 143 expanded)
%              Depth                    :   21
%              Number of atoms          :  547 (3730 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1426,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f225,f276,f310,f336,f378,f1207,f1220,f1246,f1425])).

fof(f1425,plain,(
    spl7_32 ),
    inference(avatar_contradiction_clause,[],[f1422])).

fof(f1422,plain,
    ( $false
    | spl7_32 ),
    inference(unit_resulting_resolution,[],[f283,f48,f1260,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1260,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | spl7_32 ),
    inference(resolution,[],[f1206,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1206,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_32 ),
    inference(avatar_component_clause,[],[f1204])).

fof(f1204,plain,
    ( spl7_32
  <=> m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f283,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f167,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f167,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f166,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).

fof(f166,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f165,f41])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f165,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f164,f40])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f164,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f163,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f163,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f153,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f153,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f152,f38])).

fof(f152,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f151,f41])).

fof(f151,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f150,f40])).

fof(f150,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f141,f39])).

fof(f141,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f37,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f1246,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | spl7_31 ),
    inference(avatar_contradiction_clause,[],[f1245])).

fof(f1245,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_9
    | spl7_31 ),
    inference(subsumption_resolution,[],[f1244,f361])).

fof(f361,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f360,f158])).

fof(f158,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f157,f38])).

fof(f157,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f156,f41])).

fof(f156,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f155,f40])).

fof(f155,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f154,f39])).

fof(f154,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f140,f56])).

fof(f140,plain,(
    m1_connsp_2(sK3,sK0,sK1) ),
    inference(subsumption_resolution,[],[f139,f38])).

fof(f139,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK3,sK0,sK1) ),
    inference(subsumption_resolution,[],[f138,f41])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK3,sK0,sK1) ),
    inference(subsumption_resolution,[],[f137,f40])).

fof(f137,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK3,sK0,sK1) ),
    inference(subsumption_resolution,[],[f128,f39])).

fof(f128,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f35,f45])).

fof(f35,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f360,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK3)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f359,f38])).

fof(f359,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK3)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f358,f41])).

fof(f358,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK3)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f357,f40])).

fof(f357,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK3)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f347,f39])).

fof(f347,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK3)
    | ~ spl7_8 ),
    inference(resolution,[],[f309,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X2)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f309,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl7_8
  <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1244,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl7_9
    | spl7_31 ),
    inference(subsumption_resolution,[],[f1237,f392])).

fof(f392,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f391,f167])).

fof(f391,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK2)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f390,f38])).

fof(f390,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK2)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f389,f41])).

fof(f389,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK2)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f388,f40])).

fof(f388,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK2)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f379,f39])).

fof(f379,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK2)
    | ~ spl7_9 ),
    inference(resolution,[],[f377,f42])).

fof(f377,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl7_9
  <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1237,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK3)
    | spl7_31 ),
    inference(resolution,[],[f1202,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1202,plain,
    ( ~ r2_hidden(sK1,k3_xboole_0(sK2,sK3))
    | spl7_31 ),
    inference(avatar_component_clause,[],[f1200])).

fof(f1200,plain,
    ( spl7_31
  <=> r2_hidden(sK1,k3_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f1220,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | spl7_30 ),
    inference(avatar_contradiction_clause,[],[f1219])).

fof(f1219,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_9
    | spl7_30 ),
    inference(subsumption_resolution,[],[f1218,f158])).

fof(f1218,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_8
    | ~ spl7_9
    | spl7_30 ),
    inference(subsumption_resolution,[],[f1217,f368])).

fof(f368,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f367,f158])).

fof(f367,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK3,sK0)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f366,f38])).

fof(f366,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK3,sK0)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f365,f41])).

fof(f365,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK3,sK0)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f364,f40])).

fof(f364,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK3,sK0)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f348,f39])).

fof(f348,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK3,sK0)
    | ~ spl7_8 ),
    inference(resolution,[],[f309,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1217,plain,
    ( ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_9
    | spl7_30 ),
    inference(subsumption_resolution,[],[f1216,f167])).

fof(f1216,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_9
    | spl7_30 ),
    inference(subsumption_resolution,[],[f1215,f399])).

fof(f399,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f398,f167])).

fof(f398,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,sK0)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f397,f38])).

fof(f397,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,sK0)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f396,f41])).

fof(f396,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,sK0)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f395,f40])).

fof(f395,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,sK0)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f380,f39])).

fof(f380,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,sK0)
    | ~ spl7_9 ),
    inference(resolution,[],[f377,f43])).

fof(f1215,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_30 ),
    inference(subsumption_resolution,[],[f1214,f41])).

fof(f1214,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_30 ),
    inference(subsumption_resolution,[],[f1210,f40])).

fof(f1210,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_30 ),
    inference(resolution,[],[f1198,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

fof(f1198,plain,
    ( ~ v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)
    | spl7_30 ),
    inference(avatar_component_clause,[],[f1196])).

fof(f1196,plain,
    ( spl7_30
  <=> v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f1207,plain,
    ( ~ spl7_30
    | ~ spl7_31
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f248,f1204,f1200,f1196])).

fof(f248,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k3_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f247,f38])).

fof(f247,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k3_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f246,f41])).

fof(f246,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k3_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f245,f40])).

fof(f245,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k3_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f239,f39])).

fof(f239,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k3_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) ),
    inference(resolution,[],[f160,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ v3_pre_topc(X2,X0)
      | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f160,plain,(
    ~ r2_hidden(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(resolution,[],[f36,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f36,plain,(
    ~ m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f378,plain,
    ( spl7_9
    | spl7_5 ),
    inference(avatar_split_clause,[],[f147,f222,f375])).

fof(f222,plain,
    ( spl7_5
  <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f147,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(resolution,[],[f37,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f336,plain,
    ( ~ spl7_4
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl7_4
    | spl7_7 ),
    inference(subsumption_resolution,[],[f333,f320])).

fof(f320,plain,
    ( ! [X2,X3] : ~ r2_hidden(X2,k3_xboole_0(X3,sK3))
    | ~ spl7_4 ),
    inference(resolution,[],[f314,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f314,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f220,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f220,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl7_4
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f333,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3))
    | spl7_7 ),
    inference(resolution,[],[f275,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f275,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK2,sK3))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl7_7
  <=> v1_xboole_0(k3_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f310,plain,
    ( spl7_8
    | spl7_5 ),
    inference(avatar_split_clause,[],[f134,f222,f307])).

fof(f134,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(resolution,[],[f35,f55])).

fof(f276,plain,
    ( ~ spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f161,f222,f273])).

fof(f161,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ v1_xboole_0(k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f225,plain,
    ( spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f135,f222,f218])).

fof(f135,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f35,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:26:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (4475)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (4483)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (4481)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (4484)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (4491)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (4471)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (4500)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (4472)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (4492)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (4498)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (4493)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (4495)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (4486)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (4485)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (4470)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (4470)Refutation not found, incomplete strategy% (4470)------------------------------
% 0.20/0.54  % (4470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (4470)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (4470)Memory used [KB]: 1663
% 0.20/0.54  % (4470)Time elapsed: 0.123 s
% 0.20/0.54  % (4470)------------------------------
% 0.20/0.54  % (4470)------------------------------
% 0.20/0.54  % (4481)Refutation not found, incomplete strategy% (4481)------------------------------
% 0.20/0.54  % (4481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (4494)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (4474)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (4487)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (4476)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (4490)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (4481)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (4481)Memory used [KB]: 10618
% 0.20/0.55  % (4481)Time elapsed: 0.127 s
% 0.20/0.55  % (4481)------------------------------
% 0.20/0.55  % (4481)------------------------------
% 0.20/0.55  % (4493)Refutation not found, incomplete strategy% (4493)------------------------------
% 0.20/0.55  % (4493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (4496)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (4477)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (4479)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (4482)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (4499)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.56  % (4479)Refutation not found, incomplete strategy% (4479)------------------------------
% 1.37/0.56  % (4479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (4479)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (4479)Memory used [KB]: 10618
% 1.37/0.56  % (4479)Time elapsed: 0.150 s
% 1.37/0.56  % (4479)------------------------------
% 1.37/0.56  % (4479)------------------------------
% 1.37/0.56  % (4482)Refutation not found, incomplete strategy% (4482)------------------------------
% 1.37/0.56  % (4482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (4482)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (4482)Memory used [KB]: 10618
% 1.37/0.56  % (4482)Time elapsed: 0.148 s
% 1.37/0.56  % (4482)------------------------------
% 1.37/0.56  % (4482)------------------------------
% 1.37/0.56  % (4488)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.56  % (4488)Refutation not found, incomplete strategy% (4488)------------------------------
% 1.37/0.56  % (4488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (4488)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (4488)Memory used [KB]: 10618
% 1.37/0.56  % (4488)Time elapsed: 0.145 s
% 1.37/0.56  % (4488)------------------------------
% 1.37/0.56  % (4488)------------------------------
% 1.37/0.57  % (4478)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.57  % (4493)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.57  
% 1.37/0.57  % (4493)Memory used [KB]: 10874
% 1.37/0.57  % (4493)Time elapsed: 0.092 s
% 1.37/0.57  % (4493)------------------------------
% 1.37/0.57  % (4493)------------------------------
% 1.65/0.58  % (4473)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.65/0.60  % (4497)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.65/0.60  % (4489)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.65/0.60  % (4484)Refutation found. Thanks to Tanya!
% 1.65/0.60  % SZS status Theorem for theBenchmark
% 1.65/0.60  % SZS output start Proof for theBenchmark
% 1.65/0.60  fof(f1426,plain,(
% 1.65/0.60    $false),
% 1.65/0.60    inference(avatar_sat_refutation,[],[f225,f276,f310,f336,f378,f1207,f1220,f1246,f1425])).
% 1.65/0.60  fof(f1425,plain,(
% 1.65/0.60    spl7_32),
% 1.65/0.60    inference(avatar_contradiction_clause,[],[f1422])).
% 1.65/0.60  fof(f1422,plain,(
% 1.65/0.60    $false | spl7_32),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f283,f48,f1260,f61])).
% 1.65/0.60  fof(f61,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f34])).
% 1.65/0.60  fof(f34,plain,(
% 1.65/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.65/0.60    inference(flattening,[],[f33])).
% 1.65/0.60  fof(f33,plain,(
% 1.65/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.65/0.60    inference(ennf_transformation,[],[f4])).
% 1.65/0.60  fof(f4,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.65/0.60  fof(f1260,plain,(
% 1.65/0.60    ~r1_tarski(k3_xboole_0(sK2,sK3),u1_struct_0(sK0)) | spl7_32),
% 1.65/0.60    inference(resolution,[],[f1206,f57])).
% 1.65/0.60  fof(f57,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.65/0.60    inference(cnf_transformation,[],[f9])).
% 1.65/0.60  fof(f9,axiom,(
% 1.65/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.65/0.60  fof(f1206,plain,(
% 1.65/0.60    ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl7_32),
% 1.65/0.60    inference(avatar_component_clause,[],[f1204])).
% 1.65/0.60  fof(f1204,plain,(
% 1.65/0.60    spl7_32 <=> m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 1.65/0.60  fof(f48,plain,(
% 1.65/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f3])).
% 1.65/0.60  fof(f3,axiom,(
% 1.65/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.65/0.60  fof(f283,plain,(
% 1.65/0.60    r1_tarski(sK2,u1_struct_0(sK0))),
% 1.65/0.60    inference(resolution,[],[f167,f58])).
% 1.65/0.60  fof(f58,plain,(
% 1.65/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.65/0.60    inference(cnf_transformation,[],[f9])).
% 1.65/0.60  fof(f167,plain,(
% 1.65/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.60    inference(subsumption_resolution,[],[f166,f38])).
% 1.65/0.60  fof(f38,plain,(
% 1.65/0.60    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.65/0.60    inference(cnf_transformation,[],[f18])).
% 1.65/0.60  fof(f18,plain,(
% 1.65/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.65/0.60    inference(flattening,[],[f17])).
% 1.65/0.60  fof(f17,plain,(
% 1.65/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f16])).
% 1.65/0.60  fof(f16,negated_conjecture,(
% 1.65/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.65/0.60    inference(negated_conjecture,[],[f15])).
% 1.65/0.60  fof(f15,conjecture,(
% 1.65/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).
% 1.65/0.60  fof(f166,plain,(
% 1.65/0.60    ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.60    inference(subsumption_resolution,[],[f165,f41])).
% 1.65/0.60  fof(f41,plain,(
% 1.65/0.60    l1_pre_topc(sK0)),
% 1.65/0.60    inference(cnf_transformation,[],[f18])).
% 1.65/0.60  fof(f165,plain,(
% 1.65/0.60    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.60    inference(subsumption_resolution,[],[f164,f40])).
% 1.65/0.60  fof(f40,plain,(
% 1.65/0.60    v2_pre_topc(sK0)),
% 1.65/0.60    inference(cnf_transformation,[],[f18])).
% 1.65/0.60  fof(f164,plain,(
% 1.65/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.60    inference(subsumption_resolution,[],[f163,f39])).
% 1.65/0.60  fof(f39,plain,(
% 1.65/0.60    ~v2_struct_0(sK0)),
% 1.65/0.60    inference(cnf_transformation,[],[f18])).
% 1.65/0.60  fof(f163,plain,(
% 1.65/0.60    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.60    inference(resolution,[],[f153,f56])).
% 1.65/0.60  fof(f56,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.65/0.60    inference(cnf_transformation,[],[f28])).
% 1.65/0.60  fof(f28,plain,(
% 1.65/0.60    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/0.60    inference(flattening,[],[f27])).
% 1.65/0.60  fof(f27,plain,(
% 1.65/0.60    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f12])).
% 1.65/0.60  fof(f12,axiom,(
% 1.65/0.60    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.65/0.60  fof(f153,plain,(
% 1.65/0.60    m1_connsp_2(sK2,sK0,sK1)),
% 1.65/0.60    inference(subsumption_resolution,[],[f152,f38])).
% 1.65/0.60  fof(f152,plain,(
% 1.65/0.60    ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,sK1)),
% 1.65/0.60    inference(subsumption_resolution,[],[f151,f41])).
% 1.65/0.60  fof(f151,plain,(
% 1.65/0.60    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,sK1)),
% 1.65/0.60    inference(subsumption_resolution,[],[f150,f40])).
% 1.65/0.60  fof(f150,plain,(
% 1.65/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,sK1)),
% 1.65/0.60    inference(subsumption_resolution,[],[f141,f39])).
% 1.65/0.60  fof(f141,plain,(
% 1.65/0.60    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,sK1)),
% 1.65/0.60    inference(resolution,[],[f37,f45])).
% 1.65/0.60  fof(f45,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | m1_connsp_2(X2,X0,X1)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f22])).
% 1.65/0.60  fof(f22,plain,(
% 1.65/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/0.60    inference(flattening,[],[f21])).
% 1.65/0.60  fof(f21,plain,(
% 1.65/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f14])).
% 1.65/0.60  fof(f14,axiom,(
% 1.65/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).
% 1.65/0.60  fof(f37,plain,(
% 1.65/0.60    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.65/0.60    inference(cnf_transformation,[],[f18])).
% 1.65/0.60  fof(f1246,plain,(
% 1.65/0.60    ~spl7_8 | ~spl7_9 | spl7_31),
% 1.65/0.60    inference(avatar_contradiction_clause,[],[f1245])).
% 1.65/0.60  fof(f1245,plain,(
% 1.65/0.60    $false | (~spl7_8 | ~spl7_9 | spl7_31)),
% 1.65/0.60    inference(subsumption_resolution,[],[f1244,f361])).
% 1.65/0.60  fof(f361,plain,(
% 1.65/0.60    r2_hidden(sK1,sK3) | ~spl7_8),
% 1.65/0.60    inference(subsumption_resolution,[],[f360,f158])).
% 1.65/0.60  fof(f158,plain,(
% 1.65/0.60    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.60    inference(subsumption_resolution,[],[f157,f38])).
% 1.65/0.60  fof(f157,plain,(
% 1.65/0.60    ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.60    inference(subsumption_resolution,[],[f156,f41])).
% 1.65/0.60  fof(f156,plain,(
% 1.65/0.60    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.60    inference(subsumption_resolution,[],[f155,f40])).
% 1.65/0.60  fof(f155,plain,(
% 1.65/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.60    inference(subsumption_resolution,[],[f154,f39])).
% 1.65/0.60  fof(f154,plain,(
% 1.65/0.60    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.60    inference(resolution,[],[f140,f56])).
% 1.65/0.60  fof(f140,plain,(
% 1.65/0.60    m1_connsp_2(sK3,sK0,sK1)),
% 1.65/0.60    inference(subsumption_resolution,[],[f139,f38])).
% 1.65/0.60  fof(f139,plain,(
% 1.65/0.60    ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK3,sK0,sK1)),
% 1.65/0.60    inference(subsumption_resolution,[],[f138,f41])).
% 1.65/0.60  fof(f138,plain,(
% 1.65/0.60    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK3,sK0,sK1)),
% 1.65/0.60    inference(subsumption_resolution,[],[f137,f40])).
% 1.65/0.60  fof(f137,plain,(
% 1.65/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK3,sK0,sK1)),
% 1.65/0.60    inference(subsumption_resolution,[],[f128,f39])).
% 1.65/0.60  fof(f128,plain,(
% 1.65/0.60    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK3,sK0,sK1)),
% 1.65/0.60    inference(resolution,[],[f35,f45])).
% 1.65/0.60  fof(f35,plain,(
% 1.65/0.60    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.65/0.60    inference(cnf_transformation,[],[f18])).
% 1.65/0.60  fof(f360,plain,(
% 1.65/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK3) | ~spl7_8),
% 1.65/0.60    inference(subsumption_resolution,[],[f359,f38])).
% 1.65/0.60  fof(f359,plain,(
% 1.65/0.60    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK3) | ~spl7_8),
% 1.65/0.60    inference(subsumption_resolution,[],[f358,f41])).
% 1.65/0.60  fof(f358,plain,(
% 1.65/0.60    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK3) | ~spl7_8),
% 1.65/0.60    inference(subsumption_resolution,[],[f357,f40])).
% 1.65/0.60  fof(f357,plain,(
% 1.65/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK3) | ~spl7_8),
% 1.65/0.60    inference(subsumption_resolution,[],[f347,f39])).
% 1.65/0.60  fof(f347,plain,(
% 1.65/0.60    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK3) | ~spl7_8),
% 1.65/0.60    inference(resolution,[],[f309,f42])).
% 1.65/0.60  fof(f42,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X2) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))) )),
% 1.65/0.60    inference(cnf_transformation,[],[f20])).
% 1.65/0.60  fof(f20,plain,(
% 1.65/0.60    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/0.60    inference(flattening,[],[f19])).
% 1.65/0.60  fof(f19,plain,(
% 1.65/0.60    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f13])).
% 1.65/0.60  fof(f13,axiom,(
% 1.65/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
% 1.65/0.60  fof(f309,plain,(
% 1.65/0.60    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl7_8),
% 1.65/0.60    inference(avatar_component_clause,[],[f307])).
% 1.65/0.60  fof(f307,plain,(
% 1.65/0.60    spl7_8 <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.65/0.60  fof(f1244,plain,(
% 1.65/0.60    ~r2_hidden(sK1,sK3) | (~spl7_9 | spl7_31)),
% 1.65/0.60    inference(subsumption_resolution,[],[f1237,f392])).
% 1.65/0.60  fof(f392,plain,(
% 1.65/0.60    r2_hidden(sK1,sK2) | ~spl7_9),
% 1.65/0.60    inference(subsumption_resolution,[],[f391,f167])).
% 1.65/0.60  fof(f391,plain,(
% 1.65/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK2) | ~spl7_9),
% 1.65/0.60    inference(subsumption_resolution,[],[f390,f38])).
% 1.65/0.60  fof(f390,plain,(
% 1.65/0.60    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK2) | ~spl7_9),
% 1.65/0.60    inference(subsumption_resolution,[],[f389,f41])).
% 1.65/0.60  fof(f389,plain,(
% 1.65/0.60    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK2) | ~spl7_9),
% 1.65/0.60    inference(subsumption_resolution,[],[f388,f40])).
% 1.65/0.60  fof(f388,plain,(
% 1.65/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK2) | ~spl7_9),
% 1.65/0.60    inference(subsumption_resolution,[],[f379,f39])).
% 1.65/0.60  fof(f379,plain,(
% 1.65/0.60    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK2) | ~spl7_9),
% 1.65/0.60    inference(resolution,[],[f377,f42])).
% 1.65/0.60  fof(f377,plain,(
% 1.65/0.60    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl7_9),
% 1.65/0.60    inference(avatar_component_clause,[],[f375])).
% 1.65/0.60  fof(f375,plain,(
% 1.65/0.60    spl7_9 <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.65/0.60  fof(f1237,plain,(
% 1.65/0.60    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK3) | spl7_31),
% 1.65/0.60    inference(resolution,[],[f1202,f68])).
% 1.65/0.60  fof(f68,plain,(
% 1.65/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 1.65/0.60    inference(equality_resolution,[],[f67])).
% 1.65/0.60  fof(f67,plain,(
% 1.65/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.65/0.60    inference(cnf_transformation,[],[f2])).
% 1.65/0.60  fof(f2,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.65/0.60  fof(f1202,plain,(
% 1.65/0.60    ~r2_hidden(sK1,k3_xboole_0(sK2,sK3)) | spl7_31),
% 1.65/0.60    inference(avatar_component_clause,[],[f1200])).
% 1.65/0.60  fof(f1200,plain,(
% 1.65/0.60    spl7_31 <=> r2_hidden(sK1,k3_xboole_0(sK2,sK3))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.65/0.60  fof(f1220,plain,(
% 1.65/0.60    ~spl7_8 | ~spl7_9 | spl7_30),
% 1.65/0.60    inference(avatar_contradiction_clause,[],[f1219])).
% 1.65/0.60  fof(f1219,plain,(
% 1.65/0.60    $false | (~spl7_8 | ~spl7_9 | spl7_30)),
% 1.65/0.60    inference(subsumption_resolution,[],[f1218,f158])).
% 1.65/0.60  fof(f1218,plain,(
% 1.65/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_8 | ~spl7_9 | spl7_30)),
% 1.65/0.60    inference(subsumption_resolution,[],[f1217,f368])).
% 1.65/0.60  fof(f368,plain,(
% 1.65/0.60    v3_pre_topc(sK3,sK0) | ~spl7_8),
% 1.65/0.60    inference(subsumption_resolution,[],[f367,f158])).
% 1.65/0.60  fof(f367,plain,(
% 1.65/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK3,sK0) | ~spl7_8),
% 1.65/0.60    inference(subsumption_resolution,[],[f366,f38])).
% 1.65/0.60  fof(f366,plain,(
% 1.65/0.60    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK3,sK0) | ~spl7_8),
% 1.65/0.60    inference(subsumption_resolution,[],[f365,f41])).
% 1.65/0.60  fof(f365,plain,(
% 1.65/0.60    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK3,sK0) | ~spl7_8),
% 1.65/0.60    inference(subsumption_resolution,[],[f364,f40])).
% 1.65/0.60  fof(f364,plain,(
% 1.65/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK3,sK0) | ~spl7_8),
% 1.65/0.60    inference(subsumption_resolution,[],[f348,f39])).
% 1.65/0.60  fof(f348,plain,(
% 1.65/0.60    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK3,sK0) | ~spl7_8),
% 1.65/0.60    inference(resolution,[],[f309,f43])).
% 1.65/0.60  fof(f43,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))) )),
% 1.65/0.60    inference(cnf_transformation,[],[f20])).
% 1.65/0.60  fof(f1217,plain,(
% 1.65/0.60    ~v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_9 | spl7_30)),
% 1.65/0.60    inference(subsumption_resolution,[],[f1216,f167])).
% 1.65/0.60  fof(f1216,plain,(
% 1.65/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_9 | spl7_30)),
% 1.65/0.60    inference(subsumption_resolution,[],[f1215,f399])).
% 1.65/0.60  fof(f399,plain,(
% 1.65/0.60    v3_pre_topc(sK2,sK0) | ~spl7_9),
% 1.65/0.60    inference(subsumption_resolution,[],[f398,f167])).
% 1.65/0.60  fof(f398,plain,(
% 1.65/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2,sK0) | ~spl7_9),
% 1.65/0.60    inference(subsumption_resolution,[],[f397,f38])).
% 1.65/0.60  fof(f397,plain,(
% 1.65/0.60    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2,sK0) | ~spl7_9),
% 1.65/0.60    inference(subsumption_resolution,[],[f396,f41])).
% 1.65/0.60  fof(f396,plain,(
% 1.65/0.60    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2,sK0) | ~spl7_9),
% 1.65/0.60    inference(subsumption_resolution,[],[f395,f40])).
% 1.65/0.60  fof(f395,plain,(
% 1.65/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2,sK0) | ~spl7_9),
% 1.65/0.60    inference(subsumption_resolution,[],[f380,f39])).
% 1.65/0.60  fof(f380,plain,(
% 1.65/0.60    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2,sK0) | ~spl7_9),
% 1.65/0.60    inference(resolution,[],[f377,f43])).
% 1.65/0.60  fof(f1215,plain,(
% 1.65/0.60    ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_30),
% 1.65/0.60    inference(subsumption_resolution,[],[f1214,f41])).
% 1.65/0.60  fof(f1214,plain,(
% 1.65/0.60    ~l1_pre_topc(sK0) | ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_30),
% 1.65/0.60    inference(subsumption_resolution,[],[f1210,f40])).
% 1.65/0.60  fof(f1210,plain,(
% 1.65/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_30),
% 1.65/0.60    inference(resolution,[],[f1198,f59])).
% 1.65/0.60  fof(f59,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_xboole_0(X1,X2),X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f30])).
% 1.65/0.60  fof(f30,plain,(
% 1.65/0.60    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.65/0.60    inference(flattening,[],[f29])).
% 1.65/0.60  fof(f29,plain,(
% 1.65/0.60    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f11])).
% 1.65/0.60  fof(f11,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).
% 1.65/0.60  fof(f1198,plain,(
% 1.65/0.60    ~v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) | spl7_30),
% 1.65/0.60    inference(avatar_component_clause,[],[f1196])).
% 1.65/0.60  fof(f1196,plain,(
% 1.65/0.60    spl7_30 <=> v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 1.65/0.60  fof(f1207,plain,(
% 1.65/0.60    ~spl7_30 | ~spl7_31 | ~spl7_32),
% 1.65/0.60    inference(avatar_split_clause,[],[f248,f1204,f1200,f1196])).
% 1.65/0.60  fof(f248,plain,(
% 1.65/0.60    ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k3_xboole_0(sK2,sK3)) | ~v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)),
% 1.65/0.60    inference(subsumption_resolution,[],[f247,f38])).
% 1.65/0.60  fof(f247,plain,(
% 1.65/0.60    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k3_xboole_0(sK2,sK3)) | ~v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)),
% 1.65/0.60    inference(subsumption_resolution,[],[f246,f41])).
% 1.65/0.60  fof(f246,plain,(
% 1.65/0.60    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k3_xboole_0(sK2,sK3)) | ~v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)),
% 1.65/0.60    inference(subsumption_resolution,[],[f245,f40])).
% 1.65/0.60  fof(f245,plain,(
% 1.65/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k3_xboole_0(sK2,sK3)) | ~v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)),
% 1.65/0.60    inference(subsumption_resolution,[],[f239,f39])).
% 1.65/0.60  fof(f239,plain,(
% 1.65/0.60    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k3_xboole_0(sK2,sK3)) | ~v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)),
% 1.65/0.60    inference(resolution,[],[f160,f44])).
% 1.65/0.60  fof(f44,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~v3_pre_topc(X2,X0) | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))) )),
% 1.65/0.60    inference(cnf_transformation,[],[f20])).
% 1.65/0.60  fof(f160,plain,(
% 1.65/0.60    ~r2_hidden(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.65/0.60    inference(resolution,[],[f36,f54])).
% 1.65/0.60  fof(f54,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f24])).
% 1.65/0.60  fof(f24,plain,(
% 1.65/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.65/0.60    inference(ennf_transformation,[],[f7])).
% 1.65/0.60  fof(f7,axiom,(
% 1.65/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.65/0.60  fof(f36,plain,(
% 1.65/0.60    ~m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.65/0.60    inference(cnf_transformation,[],[f18])).
% 1.65/0.60  fof(f378,plain,(
% 1.65/0.60    spl7_9 | spl7_5),
% 1.65/0.60    inference(avatar_split_clause,[],[f147,f222,f375])).
% 1.65/0.60  fof(f222,plain,(
% 1.65/0.60    spl7_5 <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.65/0.60  fof(f147,plain,(
% 1.65/0.60    v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.65/0.60    inference(resolution,[],[f37,f55])).
% 1.65/0.60  fof(f55,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f26])).
% 1.65/0.60  fof(f26,plain,(
% 1.65/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.65/0.60    inference(flattening,[],[f25])).
% 1.65/0.60  fof(f25,plain,(
% 1.65/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.65/0.60    inference(ennf_transformation,[],[f8])).
% 1.65/0.60  fof(f8,axiom,(
% 1.65/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.65/0.60  fof(f336,plain,(
% 1.65/0.60    ~spl7_4 | spl7_7),
% 1.65/0.60    inference(avatar_contradiction_clause,[],[f335])).
% 1.65/0.60  fof(f335,plain,(
% 1.65/0.60    $false | (~spl7_4 | spl7_7)),
% 1.65/0.60    inference(subsumption_resolution,[],[f333,f320])).
% 1.65/0.60  fof(f320,plain,(
% 1.65/0.60    ( ! [X2,X3] : (~r2_hidden(X2,k3_xboole_0(X3,sK3))) ) | ~spl7_4),
% 1.65/0.60    inference(resolution,[],[f314,f69])).
% 1.65/0.60  fof(f69,plain,(
% 1.65/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 1.65/0.60    inference(equality_resolution,[],[f66])).
% 1.65/0.60  fof(f66,plain,(
% 1.65/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.65/0.60    inference(cnf_transformation,[],[f2])).
% 1.65/0.60  fof(f314,plain,(
% 1.65/0.60    ( ! [X3] : (~r2_hidden(X3,sK3)) ) | ~spl7_4),
% 1.65/0.60    inference(resolution,[],[f220,f47])).
% 1.65/0.60  fof(f47,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f1])).
% 1.65/0.60  fof(f1,axiom,(
% 1.65/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.65/0.60  fof(f220,plain,(
% 1.65/0.60    v1_xboole_0(sK3) | ~spl7_4),
% 1.65/0.60    inference(avatar_component_clause,[],[f218])).
% 1.65/0.60  fof(f218,plain,(
% 1.65/0.60    spl7_4 <=> v1_xboole_0(sK3)),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.65/0.60  fof(f333,plain,(
% 1.65/0.60    r2_hidden(sK4(k3_xboole_0(sK2,sK3)),k3_xboole_0(sK2,sK3)) | spl7_7),
% 1.65/0.60    inference(resolution,[],[f275,f46])).
% 1.65/0.60  fof(f46,plain,(
% 1.65/0.60    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f1])).
% 1.65/0.60  fof(f275,plain,(
% 1.65/0.60    ~v1_xboole_0(k3_xboole_0(sK2,sK3)) | spl7_7),
% 1.65/0.60    inference(avatar_component_clause,[],[f273])).
% 1.65/0.60  fof(f273,plain,(
% 1.65/0.60    spl7_7 <=> v1_xboole_0(k3_xboole_0(sK2,sK3))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.65/0.60  fof(f310,plain,(
% 1.65/0.60    spl7_8 | spl7_5),
% 1.65/0.60    inference(avatar_split_clause,[],[f134,f222,f307])).
% 1.65/0.60  fof(f134,plain,(
% 1.65/0.60    v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.65/0.60    inference(resolution,[],[f35,f55])).
% 1.65/0.60  fof(f276,plain,(
% 1.65/0.60    ~spl7_7 | ~spl7_5),
% 1.65/0.60    inference(avatar_split_clause,[],[f161,f222,f273])).
% 1.65/0.60  fof(f161,plain,(
% 1.65/0.60    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~v1_xboole_0(k3_xboole_0(sK2,sK3))),
% 1.65/0.60    inference(resolution,[],[f36,f50])).
% 1.65/0.60  fof(f50,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~v1_xboole_0(X1) | m1_subset_1(X1,X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f23])).
% 1.65/0.60  fof(f23,plain,(
% 1.65/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f5])).
% 1.65/0.60  fof(f5,axiom,(
% 1.65/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.65/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.65/0.60  fof(f225,plain,(
% 1.65/0.60    spl7_4 | ~spl7_5),
% 1.65/0.60    inference(avatar_split_clause,[],[f135,f222,f218])).
% 1.65/0.60  fof(f135,plain,(
% 1.65/0.60    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(sK3)),
% 1.65/0.60    inference(resolution,[],[f35,f51])).
% 1.65/0.60  fof(f51,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f23])).
% 1.65/0.60  % SZS output end Proof for theBenchmark
% 1.65/0.60  % (4484)------------------------------
% 1.65/0.60  % (4484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.60  % (4484)Termination reason: Refutation
% 1.65/0.60  
% 1.65/0.60  % (4484)Memory used [KB]: 6908
% 1.65/0.60  % (4484)Time elapsed: 0.181 s
% 1.65/0.60  % (4484)------------------------------
% 1.65/0.60  % (4484)------------------------------
% 1.65/0.60  % (4466)Success in time 0.236 s
%------------------------------------------------------------------------------
