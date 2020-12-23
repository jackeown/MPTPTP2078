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
% DateTime   : Thu Dec  3 13:12:38 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 184 expanded)
%              Number of leaves         :   23 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  313 ( 491 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f832,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f99,f103,f151,f155,f160,f164,f272,f310,f318,f425,f506,f831])).

fof(f831,plain,
    ( spl2_9
    | ~ spl2_19
    | ~ spl2_43 ),
    inference(avatar_contradiction_clause,[],[f830])).

fof(f830,plain,
    ( $false
    | spl2_9
    | ~ spl2_19
    | ~ spl2_43 ),
    inference(subsumption_resolution,[],[f829,f154])).

fof(f154,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl2_9
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f829,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_19
    | ~ spl2_43 ),
    inference(resolution,[],[f512,f271])).

fof(f271,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl2_19
  <=> r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f512,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0)
        | r1_tarski(sK1,X0) )
    | ~ spl2_43 ),
    inference(resolution,[],[f505,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f505,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f504])).

fof(f504,plain,
    ( spl2_43
  <=> r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f506,plain,
    ( spl2_43
    | ~ spl2_28
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f464,f423,f316,f504])).

fof(f316,plain,
    ( spl2_28
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f423,plain,
    ( spl2_34
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f464,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl2_28
    | ~ spl2_34 ),
    inference(resolution,[],[f459,f317])).

fof(f317,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f316])).

fof(f459,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
        | r1_tarski(sK1,X0) )
    | ~ spl2_34 ),
    inference(superposition,[],[f86,f424])).

fof(f424,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f423])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f425,plain,
    ( spl2_34
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f323,f308,f158,f101,f423])).

fof(f101,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f158,plain,
    ( spl2_10
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f308,plain,
    ( spl2_26
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f323,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f321,f309])).

fof(f309,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f308])).

fof(f321,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(resolution,[],[f113,f159])).

fof(f159,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f102,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f102,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f318,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f210,f162,f149,f93,f316])).

fof(f93,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f149,plain,
    ( spl2_8
  <=> v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f162,plain,
    ( spl2_11
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f210,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f209,f150])).

fof(f150,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f209,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f196,f94])).

fof(f94,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f196,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_11 ),
    inference(resolution,[],[f163,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(f163,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f162])).

fof(f310,plain,
    ( spl2_26
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f127,f101,f93,f308])).

fof(f127,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f112,f94])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f102,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f272,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f125,f101,f93,f270])).

fof(f125,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f110,f94])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f102,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

fof(f164,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f126,f101,f93,f162])).

fof(f126,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f111,f94])).

fof(f111,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f102,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f160,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f122,f101,f93,f158])).

fof(f122,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f107,f94])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f102,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f155,plain,
    ( ~ spl2_9
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f124,f101,f93,f153])).

fof(f124,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f123,f118])).

fof(f118,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f117,f59])).

fof(f59,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(f117,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f104,f94])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f102,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f123,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f108,f94])).

fof(f108,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f102,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f151,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f121,f101,f97,f93,f149])).

fof(f97,plain,
    ( spl2_2
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f121,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f120,f98])).

fof(f98,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f120,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v3_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f106,f94])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v3_tops_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f102,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

fof(f103,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f57,f101])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f58,f97])).

fof(f58,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f95,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f60,f93])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:07 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.53  % (24156)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (24160)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (24174)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (24186)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (24169)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (24166)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (24182)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (24168)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.56  % (24185)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.69/0.57  % (24176)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.69/0.59  % (24161)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.69/0.59  % (24181)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.69/0.59  % (24177)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.78/0.60  % (24178)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.78/0.60  % (24165)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.78/0.60  % (24159)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.78/0.60  % (24170)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.78/0.60  % (24182)Refutation found. Thanks to Tanya!
% 1.78/0.60  % SZS status Theorem for theBenchmark
% 1.78/0.60  % SZS output start Proof for theBenchmark
% 1.78/0.60  fof(f832,plain,(
% 1.78/0.60    $false),
% 1.78/0.60    inference(avatar_sat_refutation,[],[f95,f99,f103,f151,f155,f160,f164,f272,f310,f318,f425,f506,f831])).
% 1.78/0.60  fof(f831,plain,(
% 1.78/0.60    spl2_9 | ~spl2_19 | ~spl2_43),
% 1.78/0.60    inference(avatar_contradiction_clause,[],[f830])).
% 1.78/0.60  fof(f830,plain,(
% 1.78/0.60    $false | (spl2_9 | ~spl2_19 | ~spl2_43)),
% 1.78/0.60    inference(subsumption_resolution,[],[f829,f154])).
% 1.78/0.60  fof(f154,plain,(
% 1.78/0.60    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | spl2_9),
% 1.78/0.60    inference(avatar_component_clause,[],[f153])).
% 1.78/0.60  fof(f153,plain,(
% 1.78/0.60    spl2_9 <=> r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.78/0.60  fof(f829,plain,(
% 1.78/0.60    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | (~spl2_19 | ~spl2_43)),
% 1.78/0.60    inference(resolution,[],[f512,f271])).
% 1.78/0.60  fof(f271,plain,(
% 1.78/0.60    r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~spl2_19),
% 1.78/0.60    inference(avatar_component_clause,[],[f270])).
% 1.78/0.60  fof(f270,plain,(
% 1.78/0.60    spl2_19 <=> r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.78/0.60  fof(f512,plain,(
% 1.78/0.60    ( ! [X0] : (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) | r1_tarski(sK1,X0)) ) | ~spl2_43),
% 1.78/0.60    inference(resolution,[],[f505,f75])).
% 1.78/0.60  fof(f75,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f47])).
% 1.78/0.60  fof(f47,plain,(
% 1.78/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.78/0.60    inference(flattening,[],[f46])).
% 1.78/0.60  fof(f46,plain,(
% 1.78/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.78/0.60    inference(ennf_transformation,[],[f6])).
% 1.78/0.60  fof(f6,axiom,(
% 1.78/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.78/0.60  fof(f505,plain,(
% 1.78/0.60    r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~spl2_43),
% 1.78/0.60    inference(avatar_component_clause,[],[f504])).
% 1.78/0.60  fof(f504,plain,(
% 1.78/0.60    spl2_43 <=> r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 1.78/0.60  fof(f506,plain,(
% 1.78/0.60    spl2_43 | ~spl2_28 | ~spl2_34),
% 1.78/0.60    inference(avatar_split_clause,[],[f464,f423,f316,f504])).
% 1.78/0.60  fof(f316,plain,(
% 1.78/0.60    spl2_28 <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 1.78/0.60  fof(f423,plain,(
% 1.78/0.60    spl2_34 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 1.78/0.60  fof(f464,plain,(
% 1.78/0.60    r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | (~spl2_28 | ~spl2_34)),
% 1.78/0.60    inference(resolution,[],[f459,f317])).
% 1.78/0.60  fof(f317,plain,(
% 1.78/0.60    r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~spl2_28),
% 1.78/0.60    inference(avatar_component_clause,[],[f316])).
% 1.78/0.60  fof(f459,plain,(
% 1.78/0.60    ( ! [X0] : (~r1_tarski(k2_pre_topc(sK0,sK1),X0) | r1_tarski(sK1,X0)) ) | ~spl2_34),
% 1.78/0.60    inference(superposition,[],[f86,f424])).
% 1.78/0.60  fof(f424,plain,(
% 1.78/0.60    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_34),
% 1.78/0.60    inference(avatar_component_clause,[],[f423])).
% 1.78/0.60  fof(f86,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f54])).
% 1.78/0.60  fof(f54,plain,(
% 1.78/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.78/0.60    inference(ennf_transformation,[],[f4])).
% 1.78/0.60  fof(f4,axiom,(
% 1.78/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.78/0.60  fof(f425,plain,(
% 1.78/0.60    spl2_34 | ~spl2_3 | ~spl2_10 | ~spl2_26),
% 1.78/0.60    inference(avatar_split_clause,[],[f323,f308,f158,f101,f423])).
% 1.78/0.60  fof(f101,plain,(
% 1.78/0.60    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.78/0.60  fof(f158,plain,(
% 1.78/0.60    spl2_10 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.78/0.60  fof(f308,plain,(
% 1.78/0.60    spl2_26 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.78/0.60  fof(f323,plain,(
% 1.78/0.60    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_10 | ~spl2_26)),
% 1.78/0.60    inference(forward_demodulation,[],[f321,f309])).
% 1.78/0.60  fof(f309,plain,(
% 1.78/0.60    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_26),
% 1.78/0.60    inference(avatar_component_clause,[],[f308])).
% 1.78/0.60  fof(f321,plain,(
% 1.78/0.60    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_10)),
% 1.78/0.60    inference(resolution,[],[f113,f159])).
% 1.78/0.60  fof(f159,plain,(
% 1.78/0.60    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_10),
% 1.78/0.60    inference(avatar_component_clause,[],[f158])).
% 1.78/0.60  fof(f113,plain,(
% 1.78/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 1.78/0.60    inference(resolution,[],[f102,f89])).
% 1.78/0.60  fof(f89,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f56])).
% 1.78/0.60  fof(f56,plain,(
% 1.78/0.60    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.78/0.60    inference(flattening,[],[f55])).
% 1.78/0.60  fof(f55,plain,(
% 1.78/0.60    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.78/0.60    inference(ennf_transformation,[],[f17])).
% 1.78/0.60  fof(f17,axiom,(
% 1.78/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.78/0.60  fof(f102,plain,(
% 1.78/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.78/0.60    inference(avatar_component_clause,[],[f101])).
% 1.78/0.60  fof(f318,plain,(
% 1.78/0.60    spl2_28 | ~spl2_1 | ~spl2_8 | ~spl2_11),
% 1.78/0.60    inference(avatar_split_clause,[],[f210,f162,f149,f93,f316])).
% 1.78/0.60  fof(f93,plain,(
% 1.78/0.60    spl2_1 <=> l1_pre_topc(sK0)),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.78/0.60  fof(f149,plain,(
% 1.78/0.60    spl2_8 <=> v2_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.78/0.60  fof(f162,plain,(
% 1.78/0.60    spl2_11 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.78/0.60  fof(f210,plain,(
% 1.78/0.60    r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | (~spl2_1 | ~spl2_8 | ~spl2_11)),
% 1.78/0.60    inference(subsumption_resolution,[],[f209,f150])).
% 1.78/0.60  fof(f150,plain,(
% 1.78/0.60    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~spl2_8),
% 1.78/0.60    inference(avatar_component_clause,[],[f149])).
% 1.78/0.60  fof(f209,plain,(
% 1.78/0.60    r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_11)),
% 1.78/0.60    inference(subsumption_resolution,[],[f196,f94])).
% 1.78/0.60  fof(f94,plain,(
% 1.78/0.60    l1_pre_topc(sK0) | ~spl2_1),
% 1.78/0.60    inference(avatar_component_clause,[],[f93])).
% 1.78/0.60  fof(f196,plain,(
% 1.78/0.60    ~l1_pre_topc(sK0) | r1_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~spl2_11),
% 1.78/0.60    inference(resolution,[],[f163,f74])).
% 1.78/0.60  fof(f74,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f45])).
% 1.78/0.60  fof(f45,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f29])).
% 1.78/0.60  fof(f29,axiom,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).
% 1.78/0.60  fof(f163,plain,(
% 1.78/0.60    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_11),
% 1.78/0.60    inference(avatar_component_clause,[],[f162])).
% 1.78/0.60  fof(f310,plain,(
% 1.78/0.60    spl2_26 | ~spl2_1 | ~spl2_3),
% 1.78/0.60    inference(avatar_split_clause,[],[f127,f101,f93,f308])).
% 1.78/0.60  fof(f127,plain,(
% 1.78/0.60    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_3)),
% 1.78/0.60    inference(subsumption_resolution,[],[f112,f94])).
% 1.78/0.60  fof(f112,plain,(
% 1.78/0.60    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_3),
% 1.78/0.60    inference(resolution,[],[f102,f85])).
% 1.78/0.60  fof(f85,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.78/0.60    inference(cnf_transformation,[],[f53])).
% 1.78/0.60  fof(f53,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f27])).
% 1.78/0.60  fof(f27,axiom,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.78/0.60  fof(f272,plain,(
% 1.78/0.60    spl2_19 | ~spl2_1 | ~spl2_3),
% 1.78/0.60    inference(avatar_split_clause,[],[f125,f101,f93,f270])).
% 1.78/0.60  fof(f125,plain,(
% 1.78/0.60    r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_3)),
% 1.78/0.60    inference(subsumption_resolution,[],[f110,f94])).
% 1.78/0.60  fof(f110,plain,(
% 1.78/0.60    ~l1_pre_topc(sK0) | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~spl2_3),
% 1.78/0.60    inference(resolution,[],[f102,f83])).
% 1.78/0.60  fof(f83,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))) )),
% 1.78/0.60    inference(cnf_transformation,[],[f50])).
% 1.78/0.60  fof(f50,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f28])).
% 1.78/0.60  fof(f28,axiom,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).
% 1.78/0.60  fof(f164,plain,(
% 1.78/0.60    spl2_11 | ~spl2_1 | ~spl2_3),
% 1.78/0.60    inference(avatar_split_clause,[],[f126,f101,f93,f162])).
% 1.78/0.60  fof(f126,plain,(
% 1.78/0.60    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_3)),
% 1.78/0.60    inference(subsumption_resolution,[],[f111,f94])).
% 1.78/0.60  fof(f111,plain,(
% 1.78/0.60    ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.78/0.60    inference(resolution,[],[f102,f84])).
% 1.78/0.60  fof(f84,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.78/0.60    inference(cnf_transformation,[],[f52])).
% 1.78/0.60  fof(f52,plain,(
% 1.78/0.60    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(flattening,[],[f51])).
% 1.78/0.60  fof(f51,plain,(
% 1.78/0.60    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.78/0.60    inference(ennf_transformation,[],[f22])).
% 1.78/0.60  fof(f22,axiom,(
% 1.78/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.78/0.60  fof(f160,plain,(
% 1.78/0.60    spl2_10 | ~spl2_1 | ~spl2_3),
% 1.78/0.60    inference(avatar_split_clause,[],[f122,f101,f93,f158])).
% 1.78/0.60  fof(f122,plain,(
% 1.78/0.60    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_3)),
% 1.78/0.60    inference(subsumption_resolution,[],[f107,f94])).
% 1.78/0.60  fof(f107,plain,(
% 1.78/0.60    ~l1_pre_topc(sK0) | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.78/0.60    inference(resolution,[],[f102,f72])).
% 1.78/0.60  fof(f72,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.78/0.60    inference(cnf_transformation,[],[f44])).
% 1.78/0.60  fof(f44,plain,(
% 1.78/0.60    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(flattening,[],[f43])).
% 1.78/0.60  fof(f43,plain,(
% 1.78/0.60    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.78/0.60    inference(ennf_transformation,[],[f25])).
% 1.78/0.60  fof(f25,axiom,(
% 1.78/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.78/0.60  fof(f155,plain,(
% 1.78/0.60    ~spl2_9 | ~spl2_1 | ~spl2_3),
% 1.78/0.60    inference(avatar_split_clause,[],[f124,f101,f93,f153])).
% 1.78/0.60  fof(f124,plain,(
% 1.78/0.60    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_3)),
% 1.78/0.60    inference(subsumption_resolution,[],[f123,f118])).
% 1.78/0.60  fof(f118,plain,(
% 1.78/0.60    ~v2_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_3)),
% 1.78/0.60    inference(subsumption_resolution,[],[f117,f59])).
% 1.78/0.60  fof(f59,plain,(
% 1.78/0.60    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.78/0.60    inference(cnf_transformation,[],[f33])).
% 1.78/0.60  fof(f33,plain,(
% 1.78/0.60    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.78/0.60    inference(flattening,[],[f32])).
% 1.78/0.60  fof(f32,plain,(
% 1.78/0.60    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f31])).
% 1.78/0.60  fof(f31,negated_conjecture,(
% 1.78/0.60    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.78/0.60    inference(negated_conjecture,[],[f30])).
% 1.78/0.60  fof(f30,conjecture,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).
% 1.78/0.60  fof(f117,plain,(
% 1.78/0.60    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v2_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_3)),
% 1.78/0.60    inference(subsumption_resolution,[],[f104,f94])).
% 1.78/0.60  fof(f104,plain,(
% 1.78/0.60    ~l1_pre_topc(sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v2_tops_1(sK1,sK0) | ~spl2_3),
% 1.78/0.60    inference(resolution,[],[f102,f62])).
% 1.78/0.60  fof(f62,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f34])).
% 1.78/0.60  fof(f34,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f23])).
% 1.78/0.60  fof(f23,axiom,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 1.78/0.60  fof(f123,plain,(
% 1.78/0.60    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_3)),
% 1.78/0.60    inference(subsumption_resolution,[],[f108,f94])).
% 1.78/0.60  fof(f108,plain,(
% 1.78/0.60    ~l1_pre_topc(sK0) | ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0) | ~spl2_3),
% 1.78/0.60    inference(resolution,[],[f102,f73])).
% 1.78/0.60  fof(f73,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f45])).
% 1.78/0.60  fof(f151,plain,(
% 1.78/0.60    spl2_8 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 1.78/0.60    inference(avatar_split_clause,[],[f121,f101,f97,f93,f149])).
% 1.78/0.60  fof(f97,plain,(
% 1.78/0.60    spl2_2 <=> v3_tops_1(sK1,sK0)),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.78/0.60  fof(f121,plain,(
% 1.78/0.60    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 1.78/0.60    inference(subsumption_resolution,[],[f120,f98])).
% 1.78/0.60  fof(f98,plain,(
% 1.78/0.60    v3_tops_1(sK1,sK0) | ~spl2_2),
% 1.78/0.60    inference(avatar_component_clause,[],[f97])).
% 1.78/0.60  fof(f120,plain,(
% 1.78/0.60    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v3_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_3)),
% 1.78/0.60    inference(subsumption_resolution,[],[f106,f94])).
% 1.78/0.60  fof(f106,plain,(
% 1.78/0.60    ~l1_pre_topc(sK0) | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v3_tops_1(sK1,sK0) | ~spl2_3),
% 1.78/0.60    inference(resolution,[],[f102,f69])).
% 1.78/0.60  fof(f69,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f42])).
% 1.78/0.60  fof(f42,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f24])).
% 1.78/0.60  fof(f24,axiom,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).
% 1.78/0.60  fof(f103,plain,(
% 1.78/0.60    spl2_3),
% 1.78/0.60    inference(avatar_split_clause,[],[f57,f101])).
% 1.78/0.60  fof(f57,plain,(
% 1.78/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.60    inference(cnf_transformation,[],[f33])).
% 1.78/0.60  fof(f99,plain,(
% 1.78/0.60    spl2_2),
% 1.78/0.60    inference(avatar_split_clause,[],[f58,f97])).
% 1.78/0.60  fof(f58,plain,(
% 1.78/0.60    v3_tops_1(sK1,sK0)),
% 1.78/0.60    inference(cnf_transformation,[],[f33])).
% 1.78/0.60  fof(f95,plain,(
% 1.78/0.60    spl2_1),
% 1.78/0.60    inference(avatar_split_clause,[],[f60,f93])).
% 1.78/0.60  fof(f60,plain,(
% 1.78/0.60    l1_pre_topc(sK0)),
% 1.78/0.60    inference(cnf_transformation,[],[f33])).
% 1.78/0.60  % SZS output end Proof for theBenchmark
% 1.78/0.60  % (24182)------------------------------
% 1.78/0.60  % (24182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (24182)Termination reason: Refutation
% 1.78/0.60  
% 1.78/0.60  % (24182)Memory used [KB]: 6780
% 1.78/0.60  % (24182)Time elapsed: 0.185 s
% 1.78/0.60  % (24182)------------------------------
% 1.78/0.60  % (24182)------------------------------
% 1.78/0.60  % (24173)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.78/0.61  % (24149)Success in time 0.248 s
%------------------------------------------------------------------------------
