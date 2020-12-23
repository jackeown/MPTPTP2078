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
% DateTime   : Thu Dec  3 13:11:07 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 202 expanded)
%              Number of leaves         :   28 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  334 ( 586 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f299,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f112,f126,f132,f143,f163,f181,f197,f273,f288,f298])).

fof(f298,plain,(
    spl3_23 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl3_23 ),
    inference(subsumption_resolution,[],[f295,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f295,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl3_23 ),
    inference(resolution,[],[f287,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f287,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl3_23
  <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f288,plain,
    ( ~ spl3_23
    | ~ spl3_2
    | ~ spl3_3
    | spl3_21 ),
    inference(avatar_split_clause,[],[f283,f270,f65,f60,f285])).

fof(f60,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f270,plain,
    ( spl3_21
  <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f283,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_21 ),
    inference(subsumption_resolution,[],[f282,f67])).

fof(f67,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f282,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_21 ),
    inference(subsumption_resolution,[],[f281,f62])).

fof(f62,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f281,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_21 ),
    inference(superposition,[],[f272,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f272,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f270])).

fof(f273,plain,
    ( ~ spl3_12
    | ~ spl3_21
    | ~ spl3_2
    | ~ spl3_4
    | spl3_10 ),
    inference(avatar_split_clause,[],[f268,f140,f70,f60,f270,f156])).

fof(f156,plain,
    ( spl3_12
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f70,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f140,plain,
    ( spl3_10
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f268,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f267,f72])).

fof(f72,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f267,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | spl3_10 ),
    inference(subsumption_resolution,[],[f265,f62])).

fof(f265,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(resolution,[],[f142,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f142,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f197,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(subsumption_resolution,[],[f195,f67])).

fof(f195,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_13 ),
    inference(subsumption_resolution,[],[f194,f62])).

fof(f194,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_13 ),
    inference(subsumption_resolution,[],[f193,f84])).

fof(f84,plain,(
    ! [X4,X3] : r1_tarski(X3,k2_xboole_0(X3,X4)) ),
    inference(subsumption_resolution,[],[f82,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f82,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k1_xboole_0,X4)
      | r1_tarski(X3,k2_xboole_0(X3,X4)) ) ),
    inference(superposition,[],[f40,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f50,f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f50,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f193,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_13 ),
    inference(superposition,[],[f162,f47])).

fof(f162,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl3_13
  <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f181,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_12 ),
    inference(subsumption_resolution,[],[f179,f67])).

fof(f179,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_12 ),
    inference(subsumption_resolution,[],[f176,f62])).

fof(f176,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_12 ),
    inference(resolution,[],[f158,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f158,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f163,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_split_clause,[],[f154,f136,f70,f65,f160,f156])).

fof(f136,plain,
    ( spl3_9
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f154,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f153,f72])).

fof(f153,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f151,f67])).

fof(f151,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f138,f45])).

fof(f138,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f143,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | spl3_7 ),
    inference(avatar_split_clause,[],[f133,f109,f140,f136])).

fof(f109,plain,
    ( spl3_7
  <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f133,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_7 ),
    inference(resolution,[],[f111,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f111,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f132,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | spl3_6 ),
    inference(subsumption_resolution,[],[f130,f72])).

fof(f130,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | spl3_6 ),
    inference(subsumption_resolution,[],[f128,f62])).

fof(f128,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_6 ),
    inference(resolution,[],[f107,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f107,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_6
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f126,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f124,f72])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_5 ),
    inference(subsumption_resolution,[],[f122,f67])).

fof(f122,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_5 ),
    inference(resolution,[],[f103,f49])).

fof(f103,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_5
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f112,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | spl3_1 ),
    inference(avatar_split_clause,[],[f96,f55,f109,f105,f101])).

fof(f55,plain,
    ( spl3_1
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f96,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(superposition,[],[f57,f47])).

fof(f57,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f73,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(f68,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f37,f60])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f38,f55])).

fof(f38,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 15:50:21 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.48  % (27196)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.49  % (27188)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.49  % (27188)Refutation not found, incomplete strategy% (27188)------------------------------
% 0.22/0.49  % (27188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (27188)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (27188)Memory used [KB]: 10746
% 0.22/0.50  % (27188)Time elapsed: 0.068 s
% 0.22/0.50  % (27188)------------------------------
% 0.22/0.50  % (27188)------------------------------
% 0.22/0.51  % (27184)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.16/0.53  % (27190)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.16/0.53  % (27178)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.16/0.53  % (27185)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.16/0.53  % (27182)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.16/0.54  % (27207)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.16/0.54  % (27207)Refutation not found, incomplete strategy% (27207)------------------------------
% 1.16/0.54  % (27207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.54  % (27207)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.54  
% 1.16/0.54  % (27207)Memory used [KB]: 1663
% 1.16/0.54  % (27207)Time elapsed: 0.083 s
% 1.16/0.54  % (27207)------------------------------
% 1.16/0.54  % (27207)------------------------------
% 1.16/0.54  % (27192)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.16/0.54  % (27206)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.16/0.54  % (27206)Refutation not found, incomplete strategy% (27206)------------------------------
% 1.16/0.54  % (27206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.54  % (27206)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.54  
% 1.16/0.54  % (27206)Memory used [KB]: 10746
% 1.16/0.54  % (27206)Time elapsed: 0.110 s
% 1.16/0.54  % (27206)------------------------------
% 1.16/0.54  % (27206)------------------------------
% 1.16/0.54  % (27193)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.16/0.54  % (27197)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.16/0.54  % (27198)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.16/0.54  % (27183)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.55  % (27201)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.55  % (27200)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.55  % (27189)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.55  % (27181)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.31/0.55  % (27202)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.55  % (27191)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.31/0.55  % (27205)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.55  % (27199)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.55  % (27179)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.31/0.56  % (27180)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.31/0.56  % (27194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.31/0.56  % (27194)Refutation not found, incomplete strategy% (27194)------------------------------
% 1.31/0.56  % (27194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (27194)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (27194)Memory used [KB]: 10618
% 1.31/0.56  % (27194)Time elapsed: 0.139 s
% 1.31/0.56  % (27194)------------------------------
% 1.31/0.56  % (27194)------------------------------
% 1.31/0.57  % (27186)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.31/0.57  % (27204)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.57  % (27199)Refutation found. Thanks to Tanya!
% 1.31/0.57  % SZS status Theorem for theBenchmark
% 1.31/0.57  % SZS output start Proof for theBenchmark
% 1.31/0.57  fof(f299,plain,(
% 1.31/0.57    $false),
% 1.31/0.57    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f112,f126,f132,f143,f163,f181,f197,f273,f288,f298])).
% 1.31/0.57  fof(f298,plain,(
% 1.31/0.57    spl3_23),
% 1.31/0.57    inference(avatar_contradiction_clause,[],[f297])).
% 1.31/0.57  fof(f297,plain,(
% 1.31/0.57    $false | spl3_23),
% 1.31/0.57    inference(subsumption_resolution,[],[f295,f52])).
% 1.31/0.57  fof(f52,plain,(
% 1.31/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.57    inference(equality_resolution,[],[f43])).
% 1.31/0.57  fof(f43,plain,(
% 1.31/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.57    inference(cnf_transformation,[],[f34])).
% 1.31/0.57  fof(f34,plain,(
% 1.31/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.57    inference(flattening,[],[f33])).
% 1.31/0.57  fof(f33,plain,(
% 1.31/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.57    inference(nnf_transformation,[],[f1])).
% 1.31/0.57  fof(f1,axiom,(
% 1.31/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.57  fof(f295,plain,(
% 1.31/0.57    ~r1_tarski(sK2,sK2) | spl3_23),
% 1.31/0.57    inference(resolution,[],[f287,f41])).
% 1.31/0.57  fof(f41,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f20])).
% 1.31/0.57  fof(f20,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.31/0.57    inference(ennf_transformation,[],[f2])).
% 1.31/0.57  fof(f2,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.31/0.57  fof(f287,plain,(
% 1.31/0.57    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | spl3_23),
% 1.31/0.57    inference(avatar_component_clause,[],[f285])).
% 1.31/0.57  fof(f285,plain,(
% 1.31/0.57    spl3_23 <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.31/0.57  fof(f288,plain,(
% 1.31/0.57    ~spl3_23 | ~spl3_2 | ~spl3_3 | spl3_21),
% 1.31/0.57    inference(avatar_split_clause,[],[f283,f270,f65,f60,f285])).
% 1.31/0.57  fof(f60,plain,(
% 1.31/0.57    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.31/0.57  fof(f65,plain,(
% 1.31/0.57    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.31/0.57  fof(f270,plain,(
% 1.31/0.57    spl3_21 <=> r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.31/0.57  fof(f283,plain,(
% 1.31/0.57    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_3 | spl3_21)),
% 1.31/0.57    inference(subsumption_resolution,[],[f282,f67])).
% 1.31/0.57  fof(f67,plain,(
% 1.31/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 1.31/0.57    inference(avatar_component_clause,[],[f65])).
% 1.31/0.57  fof(f282,plain,(
% 1.31/0.57    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_21)),
% 1.31/0.57    inference(subsumption_resolution,[],[f281,f62])).
% 1.31/0.57  fof(f62,plain,(
% 1.31/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 1.31/0.57    inference(avatar_component_clause,[],[f60])).
% 1.31/0.57  fof(f281,plain,(
% 1.31/0.57    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_21),
% 1.31/0.57    inference(superposition,[],[f272,f47])).
% 1.31/0.57  fof(f47,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.31/0.57    inference(cnf_transformation,[],[f24])).
% 1.31/0.57  fof(f24,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.57    inference(flattening,[],[f23])).
% 1.31/0.57  fof(f23,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.31/0.57    inference(ennf_transformation,[],[f11])).
% 1.31/0.57  fof(f11,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.31/0.57  fof(f272,plain,(
% 1.31/0.57    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl3_21),
% 1.31/0.57    inference(avatar_component_clause,[],[f270])).
% 1.31/0.57  fof(f273,plain,(
% 1.31/0.57    ~spl3_12 | ~spl3_21 | ~spl3_2 | ~spl3_4 | spl3_10),
% 1.31/0.57    inference(avatar_split_clause,[],[f268,f140,f70,f60,f270,f156])).
% 1.31/0.57  fof(f156,plain,(
% 1.31/0.57    spl3_12 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.31/0.57  fof(f70,plain,(
% 1.31/0.57    spl3_4 <=> l1_pre_topc(sK0)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.31/0.57  fof(f140,plain,(
% 1.31/0.57    spl3_10 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.31/0.57  fof(f268,plain,(
% 1.31/0.57    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_4 | spl3_10)),
% 1.31/0.57    inference(subsumption_resolution,[],[f267,f72])).
% 1.31/0.57  fof(f72,plain,(
% 1.31/0.57    l1_pre_topc(sK0) | ~spl3_4),
% 1.31/0.57    inference(avatar_component_clause,[],[f70])).
% 1.31/0.57  fof(f267,plain,(
% 1.31/0.57    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_2 | spl3_10)),
% 1.31/0.57    inference(subsumption_resolution,[],[f265,f62])).
% 1.31/0.57  fof(f265,plain,(
% 1.31/0.57    ~r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_10),
% 1.31/0.57    inference(resolution,[],[f142,f45])).
% 1.31/0.57  fof(f45,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f22])).
% 1.31/0.57  fof(f22,plain,(
% 1.31/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.57    inference(flattening,[],[f21])).
% 1.31/0.57  fof(f21,plain,(
% 1.31/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.57    inference(ennf_transformation,[],[f13])).
% 1.31/0.57  fof(f13,axiom,(
% 1.31/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.31/0.57  fof(f142,plain,(
% 1.31/0.57    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_10),
% 1.31/0.57    inference(avatar_component_clause,[],[f140])).
% 1.31/0.57  fof(f197,plain,(
% 1.31/0.57    ~spl3_2 | ~spl3_3 | spl3_13),
% 1.31/0.57    inference(avatar_contradiction_clause,[],[f196])).
% 1.31/0.57  fof(f196,plain,(
% 1.31/0.57    $false | (~spl3_2 | ~spl3_3 | spl3_13)),
% 1.31/0.57    inference(subsumption_resolution,[],[f195,f67])).
% 1.31/0.57  fof(f195,plain,(
% 1.31/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_13)),
% 1.31/0.57    inference(subsumption_resolution,[],[f194,f62])).
% 1.31/0.57  fof(f194,plain,(
% 1.31/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_13),
% 1.31/0.57    inference(subsumption_resolution,[],[f193,f84])).
% 1.31/0.57  fof(f84,plain,(
% 1.31/0.57    ( ! [X4,X3] : (r1_tarski(X3,k2_xboole_0(X3,X4))) )),
% 1.31/0.57    inference(subsumption_resolution,[],[f82,f46])).
% 1.31/0.57  fof(f46,plain,(
% 1.31/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f4])).
% 1.31/0.57  fof(f4,axiom,(
% 1.31/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.31/0.57  fof(f82,plain,(
% 1.31/0.57    ( ! [X4,X3] : (~r1_tarski(k1_xboole_0,X4) | r1_tarski(X3,k2_xboole_0(X3,X4))) )),
% 1.31/0.57    inference(superposition,[],[f40,f74])).
% 1.31/0.57  fof(f74,plain,(
% 1.31/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.31/0.57    inference(superposition,[],[f50,f51])).
% 1.31/0.57  fof(f51,plain,(
% 1.31/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.31/0.57    inference(cnf_transformation,[],[f3])).
% 1.31/0.57  fof(f3,axiom,(
% 1.31/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.31/0.57  fof(f50,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.31/0.57    inference(cnf_transformation,[],[f6])).
% 1.31/0.57  fof(f6,axiom,(
% 1.31/0.57    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.31/0.57  fof(f40,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.31/0.57    inference(cnf_transformation,[],[f19])).
% 1.31/0.57  fof(f19,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.31/0.57    inference(ennf_transformation,[],[f5])).
% 1.31/0.57  fof(f5,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.31/0.57  fof(f193,plain,(
% 1.31/0.57    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_13),
% 1.31/0.57    inference(superposition,[],[f162,f47])).
% 1.31/0.57  fof(f162,plain,(
% 1.31/0.57    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | spl3_13),
% 1.31/0.57    inference(avatar_component_clause,[],[f160])).
% 1.31/0.57  fof(f160,plain,(
% 1.31/0.57    spl3_13 <=> r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.31/0.57  fof(f181,plain,(
% 1.31/0.57    ~spl3_2 | ~spl3_3 | spl3_12),
% 1.31/0.57    inference(avatar_contradiction_clause,[],[f180])).
% 1.31/0.57  fof(f180,plain,(
% 1.31/0.57    $false | (~spl3_2 | ~spl3_3 | spl3_12)),
% 1.31/0.57    inference(subsumption_resolution,[],[f179,f67])).
% 1.31/0.57  fof(f179,plain,(
% 1.31/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_12)),
% 1.31/0.57    inference(subsumption_resolution,[],[f176,f62])).
% 1.31/0.57  fof(f176,plain,(
% 1.31/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_12),
% 1.31/0.57    inference(resolution,[],[f158,f48])).
% 1.31/0.57  fof(f48,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.31/0.57    inference(cnf_transformation,[],[f26])).
% 1.31/0.57  fof(f26,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.57    inference(flattening,[],[f25])).
% 1.31/0.57  fof(f25,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.31/0.57    inference(ennf_transformation,[],[f10])).
% 1.31/0.57  fof(f10,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.31/0.57  fof(f158,plain,(
% 1.31/0.57    ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_12),
% 1.31/0.57    inference(avatar_component_clause,[],[f156])).
% 1.31/0.57  fof(f163,plain,(
% 1.31/0.57    ~spl3_12 | ~spl3_13 | ~spl3_3 | ~spl3_4 | spl3_9),
% 1.31/0.57    inference(avatar_split_clause,[],[f154,f136,f70,f65,f160,f156])).
% 1.31/0.57  fof(f136,plain,(
% 1.31/0.57    spl3_9 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.31/0.57  fof(f154,plain,(
% 1.31/0.57    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_4 | spl3_9)),
% 1.31/0.57    inference(subsumption_resolution,[],[f153,f72])).
% 1.31/0.57  fof(f153,plain,(
% 1.31/0.57    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_3 | spl3_9)),
% 1.31/0.57    inference(subsumption_resolution,[],[f151,f67])).
% 1.31/0.57  fof(f151,plain,(
% 1.31/0.57    ~r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_9),
% 1.31/0.57    inference(resolution,[],[f138,f45])).
% 1.31/0.57  fof(f138,plain,(
% 1.31/0.57    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_9),
% 1.31/0.57    inference(avatar_component_clause,[],[f136])).
% 1.31/0.57  fof(f143,plain,(
% 1.31/0.57    ~spl3_9 | ~spl3_10 | spl3_7),
% 1.31/0.57    inference(avatar_split_clause,[],[f133,f109,f140,f136])).
% 1.31/0.57  fof(f109,plain,(
% 1.31/0.57    spl3_7 <=> r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.31/0.57  fof(f133,plain,(
% 1.31/0.57    ~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_7),
% 1.31/0.57    inference(resolution,[],[f111,f39])).
% 1.31/0.57  fof(f39,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f18])).
% 1.31/0.57  fof(f18,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.31/0.57    inference(flattening,[],[f17])).
% 1.31/0.57  fof(f17,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.31/0.57    inference(ennf_transformation,[],[f7])).
% 1.31/0.57  fof(f7,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.31/0.57  fof(f111,plain,(
% 1.31/0.57    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_7),
% 1.31/0.57    inference(avatar_component_clause,[],[f109])).
% 1.31/0.57  fof(f132,plain,(
% 1.31/0.57    ~spl3_2 | ~spl3_4 | spl3_6),
% 1.31/0.57    inference(avatar_contradiction_clause,[],[f131])).
% 1.31/0.57  fof(f131,plain,(
% 1.31/0.57    $false | (~spl3_2 | ~spl3_4 | spl3_6)),
% 1.31/0.57    inference(subsumption_resolution,[],[f130,f72])).
% 1.31/0.57  fof(f130,plain,(
% 1.31/0.57    ~l1_pre_topc(sK0) | (~spl3_2 | spl3_6)),
% 1.31/0.57    inference(subsumption_resolution,[],[f128,f62])).
% 1.31/0.57  fof(f128,plain,(
% 1.31/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_6),
% 1.31/0.57    inference(resolution,[],[f107,f49])).
% 1.31/0.57  fof(f49,plain,(
% 1.31/0.57    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f28])).
% 1.31/0.57  fof(f28,plain,(
% 1.31/0.57    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.31/0.57    inference(flattening,[],[f27])).
% 1.31/0.57  fof(f27,plain,(
% 1.31/0.57    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.31/0.57    inference(ennf_transformation,[],[f12])).
% 1.31/0.57  fof(f12,axiom,(
% 1.31/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.31/0.57  fof(f107,plain,(
% 1.31/0.57    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_6),
% 1.31/0.57    inference(avatar_component_clause,[],[f105])).
% 1.31/0.57  fof(f105,plain,(
% 1.31/0.57    spl3_6 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.31/0.57  fof(f126,plain,(
% 1.31/0.57    ~spl3_3 | ~spl3_4 | spl3_5),
% 1.31/0.57    inference(avatar_contradiction_clause,[],[f125])).
% 1.31/0.57  fof(f125,plain,(
% 1.31/0.57    $false | (~spl3_3 | ~spl3_4 | spl3_5)),
% 1.31/0.57    inference(subsumption_resolution,[],[f124,f72])).
% 1.31/0.57  fof(f124,plain,(
% 1.31/0.57    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_5)),
% 1.31/0.57    inference(subsumption_resolution,[],[f122,f67])).
% 1.31/0.57  fof(f122,plain,(
% 1.31/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_5),
% 1.31/0.57    inference(resolution,[],[f103,f49])).
% 1.31/0.57  fof(f103,plain,(
% 1.31/0.57    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 1.31/0.57    inference(avatar_component_clause,[],[f101])).
% 1.31/0.57  fof(f101,plain,(
% 1.31/0.57    spl3_5 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.31/0.57  fof(f112,plain,(
% 1.31/0.57    ~spl3_5 | ~spl3_6 | ~spl3_7 | spl3_1),
% 1.31/0.57    inference(avatar_split_clause,[],[f96,f55,f109,f105,f101])).
% 1.31/0.57  fof(f55,plain,(
% 1.31/0.57    spl3_1 <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.31/0.57  fof(f96,plain,(
% 1.31/0.57    ~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 1.31/0.57    inference(superposition,[],[f57,f47])).
% 1.31/0.57  fof(f57,plain,(
% 1.31/0.57    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | spl3_1),
% 1.31/0.57    inference(avatar_component_clause,[],[f55])).
% 1.31/0.57  fof(f73,plain,(
% 1.31/0.57    spl3_4),
% 1.31/0.57    inference(avatar_split_clause,[],[f35,f70])).
% 1.31/0.57  fof(f35,plain,(
% 1.31/0.57    l1_pre_topc(sK0)),
% 1.31/0.57    inference(cnf_transformation,[],[f32])).
% 1.31/0.57  fof(f32,plain,(
% 1.31/0.57    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.31/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31,f30,f29])).
% 1.31/0.57  fof(f29,plain,(
% 1.31/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.31/0.57    introduced(choice_axiom,[])).
% 1.31/0.57  fof(f30,plain,(
% 1.31/0.57    ? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.31/0.57    introduced(choice_axiom,[])).
% 1.31/0.57  fof(f31,plain,(
% 1.31/0.57    ? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.31/0.57    introduced(choice_axiom,[])).
% 1.31/0.57  fof(f16,plain,(
% 1.31/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.31/0.57    inference(ennf_transformation,[],[f15])).
% 1.31/0.57  fof(f15,negated_conjecture,(
% 1.31/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.31/0.57    inference(negated_conjecture,[],[f14])).
% 1.31/0.57  fof(f14,conjecture,(
% 1.31/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).
% 1.31/0.57  fof(f68,plain,(
% 1.31/0.57    spl3_3),
% 1.31/0.57    inference(avatar_split_clause,[],[f36,f65])).
% 1.31/0.57  fof(f36,plain,(
% 1.31/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.57    inference(cnf_transformation,[],[f32])).
% 1.31/0.57  fof(f63,plain,(
% 1.31/0.57    spl3_2),
% 1.31/0.57    inference(avatar_split_clause,[],[f37,f60])).
% 1.31/0.57  fof(f37,plain,(
% 1.31/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.57    inference(cnf_transformation,[],[f32])).
% 1.31/0.57  fof(f58,plain,(
% 1.31/0.57    ~spl3_1),
% 1.31/0.57    inference(avatar_split_clause,[],[f38,f55])).
% 1.31/0.57  fof(f38,plain,(
% 1.31/0.57    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 1.31/0.57    inference(cnf_transformation,[],[f32])).
% 1.31/0.57  % SZS output end Proof for theBenchmark
% 1.31/0.57  % (27199)------------------------------
% 1.31/0.57  % (27199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.57  % (27199)Termination reason: Refutation
% 1.31/0.57  
% 1.31/0.57  % (27199)Memory used [KB]: 6396
% 1.31/0.57  % (27199)Time elapsed: 0.107 s
% 1.31/0.57  % (27199)------------------------------
% 1.31/0.57  % (27199)------------------------------
% 1.31/0.57  % (27187)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.31/0.57  % (27177)Success in time 0.195 s
%------------------------------------------------------------------------------
