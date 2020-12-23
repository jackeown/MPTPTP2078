%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:11 EST 2020

% Result     : Theorem 7.90s
% Output     : Refutation 8.34s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 842 expanded)
%              Number of leaves         :   37 ( 265 expanded)
%              Depth                    :   19
%              Number of atoms          :  509 (2039 expanded)
%              Number of equality atoms :   34 ( 188 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f88,f93,f99,f105,f116,f123,f130,f156,f163,f702,f737,f2110,f5443,f5615,f5880,f5892,f6077,f6088,f6095,f6287,f6332,f7101])).

fof(f7101,plain,
    ( ~ spl4_2
    | ~ spl4_8
    | ~ spl4_78
    | spl4_93 ),
    inference(avatar_contradiction_clause,[],[f7100])).

fof(f7100,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_78
    | spl4_93 ),
    inference(subsumption_resolution,[],[f7099,f6337])).

fof(f6337,plain,
    ( ! [X0] : ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,sK2))
    | spl4_93 ),
    inference(resolution,[],[f6331,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f6331,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | spl4_93 ),
    inference(avatar_component_clause,[],[f6329])).

fof(f6329,plain,
    ( spl4_93
  <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f7099,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_78 ),
    inference(subsumption_resolution,[],[f7092,f3915])).

fof(f3915,plain,
    ( ! [X41,X42] : r1_tarski(k4_xboole_0(X42,X42),X41)
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(superposition,[],[f49,f3791])).

fof(f3791,plain,
    ( ! [X43,X44] : k4_xboole_0(X43,X43) = k4_xboole_0(X44,X44)
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f3775,f3656])).

fof(f3656,plain,
    ( ! [X19,X20] : r1_tarski(k4_xboole_0(X19,X19),k4_xboole_0(X20,X20))
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f3635,f3310])).

fof(f3310,plain,
    ( ! [X10] : r1_tarski(k4_xboole_0(X10,X10),u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(superposition,[],[f48,f3293])).

fof(f3293,plain,
    ( ! [X0] : u1_struct_0(sK0) = k2_xboole_0(k4_xboole_0(X0,X0),u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(resolution,[],[f934,f48])).

fof(f934,plain,
    ( ! [X10,X11,X9] :
        ( ~ r1_tarski(X9,k2_xboole_0(X10,k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),X11))))
        | u1_struct_0(sK0) = k2_xboole_0(k4_xboole_0(X9,X10),u1_struct_0(sK0)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f438,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f438,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X1,k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),X2)))
        | u1_struct_0(sK0) = k2_xboole_0(X1,u1_struct_0(sK0)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f261,f65])).

fof(f261,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k4_xboole_0(X2,sK2),k4_xboole_0(u1_struct_0(sK0),X3))
        | u1_struct_0(sK0) = k2_xboole_0(X2,u1_struct_0(sK0)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f218,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f218,plain,
    ( ! [X2,X1] :
        ( r1_tarski(X1,u1_struct_0(sK0))
        | ~ r1_tarski(k4_xboole_0(X1,sK2),k4_xboole_0(u1_struct_0(sK0),X2)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f138,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k4_xboole_0(X0,sK2),u1_struct_0(sK0))
        | r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl4_8 ),
    inference(superposition,[],[f68,f122])).

fof(f122,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_8
  <=> u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f3635,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | r1_tarski(k4_xboole_0(X1,X1),X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f1127,f48])).

fof(f1127,plain,
    ( ! [X17,X15,X18,X16] :
        ( ~ r1_tarski(X15,k2_xboole_0(X16,k2_xboole_0(k1_tops_1(sK0,X17),k4_xboole_0(X17,X18))))
        | ~ r1_tarski(X17,u1_struct_0(sK0))
        | r1_tarski(k4_xboole_0(X15,X16),X17) )
    | ~ spl4_2 ),
    inference(resolution,[],[f497,f65])).

fof(f497,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_tarski(X3,k2_xboole_0(k1_tops_1(sK0,X2),k4_xboole_0(X2,X4)))
        | r1_tarski(X3,X2)
        | ~ r1_tarski(X2,u1_struct_0(sK0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f278,f65])).

fof(f278,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(k4_xboole_0(X3,k1_tops_1(sK0,X4)),k4_xboole_0(X4,X5))
        | ~ r1_tarski(X4,u1_struct_0(sK0))
        | r1_tarski(X3,X4) )
    | ~ spl4_2 ),
    inference(resolution,[],[f229,f66])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k4_xboole_0(X0,k1_tops_1(sK0,X1)),X1)
        | r1_tarski(X0,X1)
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f190,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k4_xboole_0(X1,k1_tops_1(sK0,X0)),X0)
        | r1_tarski(X1,X0) )
    | ~ spl4_2 ),
    inference(superposition,[],[f68,f125])).

fof(f125,plain,
    ( ! [X1] :
        ( k2_xboole_0(k1_tops_1(sK0,X1),X1) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2 ),
    inference(resolution,[],[f83,f51])).

fof(f83,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2 ),
    inference(resolution,[],[f81,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

% (23906)Time limit reached!
% (23906)------------------------------
% (23906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23906)Termination reason: Time limit

% (23906)Memory used [KB]: 20596
% (23906)Time elapsed: 1.004 s
% (23906)------------------------------
% (23906)------------------------------
fof(f81,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f3775,plain,
    ( ! [X43,X44] :
        ( ~ r1_tarski(k4_xboole_0(X43,X43),k4_xboole_0(X44,X44))
        | k4_xboole_0(X43,X43) = k4_xboole_0(X44,X44) )
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f3656,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f7092,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k4_xboole_0(X1,X1),k4_xboole_0(sK1,sK2))
        | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) )
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_78 ),
    inference(superposition,[],[f6256,f3791])).

fof(f6256,plain,
    ( ! [X8] :
        ( ~ r1_tarski(k4_xboole_0(X8,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
        | r1_tarski(X8,k4_xboole_0(sK1,sK2)) )
    | ~ spl4_2
    | ~ spl4_78 ),
    inference(resolution,[],[f5933,f190])).

fof(f5933,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f5932])).

fof(f5932,plain,
    ( spl4_78
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f6332,plain,
    ( ~ spl4_93
    | ~ spl4_4
    | spl4_90 ),
    inference(avatar_split_clause,[],[f6325,f6284,f90,f6329])).

fof(f90,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f6284,plain,
    ( spl4_90
  <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f6325,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | ~ spl4_4
    | spl4_90 ),
    inference(subsumption_resolution,[],[f6324,f92])).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f6324,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_90 ),
    inference(superposition,[],[f6286,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f6286,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2)
    | spl4_90 ),
    inference(avatar_component_clause,[],[f6284])).

fof(f6287,plain,
    ( ~ spl4_90
    | ~ spl4_2
    | ~ spl4_3
    | spl4_65 ),
    inference(avatar_split_clause,[],[f6178,f5612,f85,f79,f6284])).

fof(f85,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f5612,plain,
    ( spl4_65
  <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f6178,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_65 ),
    inference(subsumption_resolution,[],[f6174,f87])).

fof(f87,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f6174,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | spl4_65 ),
    inference(superposition,[],[f6113,f125])).

fof(f6113,plain,
    ( ! [X1] : ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_xboole_0(k1_tops_1(sK0,sK2),X1))
    | spl4_65 ),
    inference(resolution,[],[f5614,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f5614,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl4_65 ),
    inference(avatar_component_clause,[],[f5612])).

fof(f6095,plain,
    ( ~ spl4_4
    | spl4_72
    | ~ spl4_78 ),
    inference(avatar_contradiction_clause,[],[f6094])).

fof(f6094,plain,
    ( $false
    | ~ spl4_4
    | spl4_72
    | ~ spl4_78 ),
    inference(subsumption_resolution,[],[f5933,f6089])).

fof(f6089,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | spl4_72 ),
    inference(subsumption_resolution,[],[f5908,f92])).

fof(f5908,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_72 ),
    inference(superposition,[],[f5879,f64])).

fof(f5879,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_72 ),
    inference(avatar_component_clause,[],[f5877])).

fof(f5877,plain,
    ( spl4_72
  <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f6088,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | spl4_85 ),
    inference(avatar_contradiction_clause,[],[f6087])).

fof(f6087,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_8
    | spl4_85 ),
    inference(subsumption_resolution,[],[f6086,f115])).

fof(f115,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_7
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f6086,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_8
    | spl4_85 ),
    inference(forward_demodulation,[],[f6082,f122])).

fof(f6082,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK2,u1_struct_0(sK0)))
    | spl4_85 ),
    inference(resolution,[],[f6076,f65])).

fof(f6076,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl4_85 ),
    inference(avatar_component_clause,[],[f6074])).

fof(f6074,plain,
    ( spl4_85
  <=> r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f6077,plain,
    ( ~ spl4_85
    | spl4_78 ),
    inference(avatar_split_clause,[],[f5940,f5932,f6074])).

fof(f5940,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl4_78 ),
    inference(resolution,[],[f5934,f58])).

fof(f5934,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_78 ),
    inference(avatar_component_clause,[],[f5932])).

fof(f5892,plain,
    ( ~ spl4_4
    | spl4_71 ),
    inference(avatar_contradiction_clause,[],[f5891])).

fof(f5891,plain,
    ( $false
    | ~ spl4_4
    | spl4_71 ),
    inference(subsumption_resolution,[],[f5890,f92])).

fof(f5890,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_71 ),
    inference(subsumption_resolution,[],[f5889,f49])).

fof(f5889,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_71 ),
    inference(superposition,[],[f5875,f64])).

fof(f5875,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | spl4_71 ),
    inference(avatar_component_clause,[],[f5873])).

fof(f5873,plain,
    ( spl4_71
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f5880,plain,
    ( ~ spl4_71
    | ~ spl4_72
    | ~ spl4_2
    | ~ spl4_4
    | spl4_64 ),
    inference(avatar_split_clause,[],[f5626,f5608,f90,f79,f5877,f5873])).

fof(f5608,plain,
    ( spl4_64
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f5626,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_64 ),
    inference(subsumption_resolution,[],[f5625,f81])).

fof(f5625,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4
    | spl4_64 ),
    inference(subsumption_resolution,[],[f5622,f92])).

fof(f5622,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | spl4_64 ),
    inference(resolution,[],[f5610,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f5610,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl4_64 ),
    inference(avatar_component_clause,[],[f5608])).

fof(f5615,plain,
    ( ~ spl4_64
    | ~ spl4_65
    | spl4_12 ),
    inference(avatar_split_clause,[],[f5570,f153,f5612,f5608])).

fof(f153,plain,
    ( spl4_12
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f5570,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl4_12 ),
    inference(resolution,[],[f155,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f155,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f153])).

fof(f5443,plain,
    ( ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | spl4_13
    | ~ spl4_30
    | ~ spl4_54 ),
    inference(avatar_contradiction_clause,[],[f5442])).

fof(f5442,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | spl4_13
    | ~ spl4_30
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f5441,f736])).

fof(f736,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f734])).

fof(f734,plain,
    ( spl4_30
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f5441,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | spl4_13
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f5440,f2109])).

fof(f2109,plain,
    ( sK1 = k2_xboole_0(sK1,sK1)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f2107])).

fof(f2107,plain,
    ( spl4_54
  <=> sK1 = k2_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f5440,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,sK1))
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | spl4_13 ),
    inference(forward_demodulation,[],[f5001,f3916])).

fof(f3916,plain,
    ( ! [X43,X44] : k2_xboole_0(X43,X43) = k2_xboole_0(X43,k4_xboole_0(X44,X44))
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(superposition,[],[f50,f3791])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f5001,plain,
    ( ! [X1341] : ~ r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,k4_xboole_0(X1341,X1341)))
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9
    | spl4_13 ),
    inference(superposition,[],[f353,f3791])).

fof(f353,plain,
    ( ! [X0] : ~ r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0)))
    | ~ spl4_9
    | spl4_13 ),
    inference(resolution,[],[f271,f65])).

fof(f271,plain,
    ( ! [X8] : ~ r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),sK1),k4_xboole_0(u1_struct_0(sK0),X8))
    | ~ spl4_9
    | spl4_13 ),
    inference(resolution,[],[f226,f162])).

fof(f162,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_13
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f226,plain,
    ( ! [X2,X1] :
        ( r1_tarski(X1,u1_struct_0(sK0))
        | ~ r1_tarski(k4_xboole_0(X1,sK1),k4_xboole_0(u1_struct_0(sK0),X2)) )
    | ~ spl4_9 ),
    inference(resolution,[],[f145,f66])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k4_xboole_0(X0,sK1),u1_struct_0(sK0))
        | r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl4_9 ),
    inference(superposition,[],[f68,f129])).

fof(f129,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_9
  <=> u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f2110,plain,
    ( spl4_54
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f2104,f699,f113,f79,f2107])).

fof(f699,plain,
    ( spl4_28
  <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f2104,plain,
    ( sK1 = k2_xboole_0(sK1,sK1)
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f2089,f701])).

fof(f701,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f699])).

fof(f2089,plain,
    ( sK1 = k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),sK1),sK1)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f650,f115])).

fof(f650,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,X2),X2),X2) = X2 )
    | ~ spl4_2 ),
    inference(resolution,[],[f427,f51])).

fof(f427,plain,
    ( ! [X3] :
        ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,X3),X3),X3)
        | ~ r1_tarski(X3,u1_struct_0(sK0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f277,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f277,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X1,k2_xboole_0(k1_tops_1(sK0,X2),X2))
        | ~ r1_tarski(X2,u1_struct_0(sK0))
        | r1_tarski(X1,X2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f229,f65])).

fof(f737,plain,
    ( spl4_30
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f719,f699,f734])).

fof(f719,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_28 ),
    inference(superposition,[],[f48,f701])).

fof(f702,plain,
    ( spl4_28
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f673,f113,f79,f699])).

fof(f673,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f435,f115])).

fof(f435,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | k2_xboole_0(k1_tops_1(sK0,X1),X1) = X1 )
    | ~ spl4_2 ),
    inference(resolution,[],[f425,f51])).

fof(f425,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,X0),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f277,f48])).

fof(f163,plain,
    ( ~ spl4_13
    | spl4_11 ),
    inference(avatar_split_clause,[],[f157,f149,f160])).

fof(f149,plain,
    ( spl4_11
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f157,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl4_11 ),
    inference(resolution,[],[f151,f58])).

fof(f151,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f156,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | spl4_6 ),
    inference(avatar_split_clause,[],[f110,f102,f153,f149])).

fof(f102,plain,
    ( spl4_6
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f110,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_6 ),
    inference(superposition,[],[f104,f64])).

fof(f104,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f130,plain,
    ( spl4_9
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f118,f113,f127])).

fof(f118,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f115,f51])).

fof(f123,plain,
    ( spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f107,f96,f120])).

fof(f96,plain,
    ( spl4_5
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f107,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))
    | ~ spl4_5 ),
    inference(resolution,[],[f98,f51])).

fof(f98,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f116,plain,
    ( spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f100,f90,f113])).

fof(f100,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f105,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f40,f102])).

fof(f40,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(f99,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f94,f85,f96])).

fof(f94,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f87,f59])).

fof(f93,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f41,f90])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f39,f85])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f43,f79])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (23905)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (23909)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (23912)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (23922)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (23933)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (23914)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (23920)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (23913)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.53  % (23910)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.53  % (23929)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.54  % (23914)Refutation not found, incomplete strategy% (23914)------------------------------
% 1.33/0.54  % (23914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (23914)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (23914)Memory used [KB]: 10746
% 1.33/0.54  % (23914)Time elapsed: 0.132 s
% 1.33/0.54  % (23914)------------------------------
% 1.33/0.54  % (23914)------------------------------
% 1.33/0.54  % (23906)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (23921)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.55  % (23923)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.55  % (23908)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.56  % (23931)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.57  % (23907)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.45/0.57  % (23924)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.57  % (23911)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.45/0.57  % (23932)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.58  % (23915)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.58  % (23928)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.58  % (23916)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.58  % (23915)Refutation not found, incomplete strategy% (23915)------------------------------
% 1.45/0.58  % (23915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (23915)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.58  
% 1.45/0.58  % (23915)Memory used [KB]: 10746
% 1.45/0.58  % (23915)Time elapsed: 0.173 s
% 1.45/0.58  % (23915)------------------------------
% 1.45/0.58  % (23915)------------------------------
% 1.45/0.58  % (23927)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.59  % (23917)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.59  % (23919)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.59  % (23918)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.45/0.59  % (23925)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.60  % (23904)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.45/0.61  % (23930)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.61  % (23926)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 2.06/0.64  % (23926)Refutation not found, incomplete strategy% (23926)------------------------------
% 2.06/0.64  % (23926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.64  % (23926)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.64  
% 2.06/0.64  % (23926)Memory used [KB]: 10746
% 2.06/0.64  % (23926)Time elapsed: 0.218 s
% 2.06/0.64  % (23926)------------------------------
% 2.06/0.64  % (23926)------------------------------
% 2.06/0.64  % (23934)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.44/0.71  % (23935)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.09/0.80  % (23936)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.40/0.82  % (23909)Time limit reached!
% 3.40/0.82  % (23909)------------------------------
% 3.40/0.82  % (23909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.82  % (23909)Termination reason: Time limit
% 3.40/0.82  
% 3.40/0.82  % (23909)Memory used [KB]: 10106
% 3.40/0.82  % (23909)Time elapsed: 0.412 s
% 3.40/0.82  % (23909)------------------------------
% 3.40/0.82  % (23909)------------------------------
% 3.60/0.92  % (23916)Time limit reached!
% 3.60/0.92  % (23916)------------------------------
% 3.60/0.92  % (23916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.92  % (23921)Time limit reached!
% 3.60/0.92  % (23921)------------------------------
% 3.60/0.92  % (23921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.13/0.93  % (23921)Termination reason: Time limit
% 4.13/0.93  
% 4.13/0.93  % (23921)Memory used [KB]: 18677
% 4.13/0.93  % (23921)Time elapsed: 0.511 s
% 4.13/0.93  % (23921)------------------------------
% 4.13/0.93  % (23921)------------------------------
% 4.13/0.93  % (23905)Time limit reached!
% 4.13/0.93  % (23905)------------------------------
% 4.13/0.93  % (23905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.13/0.93  % (23905)Termination reason: Time limit
% 4.13/0.93  
% 4.13/0.93  % (23905)Memory used [KB]: 9850
% 4.13/0.93  % (23905)Time elapsed: 0.518 s
% 4.13/0.93  % (23905)------------------------------
% 4.13/0.93  % (23905)------------------------------
% 4.13/0.93  % (23904)Time limit reached!
% 4.13/0.93  % (23904)------------------------------
% 4.13/0.93  % (23904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.13/0.93  % (23904)Termination reason: Time limit
% 4.13/0.93  % (23904)Termination phase: Saturation
% 4.13/0.93  
% 4.13/0.93  % (23904)Memory used [KB]: 4349
% 4.13/0.93  % (23904)Time elapsed: 0.500 s
% 4.13/0.93  % (23904)------------------------------
% 4.13/0.93  % (23904)------------------------------
% 4.13/0.94  % (23916)Termination reason: Time limit
% 4.13/0.94  % (23916)Termination phase: Saturation
% 4.13/0.94  
% 4.13/0.94  % (23916)Memory used [KB]: 8571
% 4.13/0.94  % (23916)Time elapsed: 0.500 s
% 4.13/0.94  % (23916)------------------------------
% 4.13/0.94  % (23916)------------------------------
% 4.13/0.94  % (23937)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.53/1.01  % (23920)Time limit reached!
% 4.53/1.01  % (23920)------------------------------
% 4.53/1.01  % (23920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/1.01  % (23920)Termination reason: Time limit
% 4.53/1.01  
% 4.53/1.01  % (23920)Memory used [KB]: 18549
% 4.53/1.01  % (23920)Time elapsed: 0.604 s
% 4.53/1.01  % (23920)------------------------------
% 4.53/1.01  % (23920)------------------------------
% 4.53/1.02  % (23911)Time limit reached!
% 4.53/1.02  % (23911)------------------------------
% 4.53/1.02  % (23911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/1.02  % (23911)Termination reason: Time limit
% 4.53/1.02  
% 4.53/1.02  % (23911)Memory used [KB]: 10874
% 4.53/1.02  % (23911)Time elapsed: 0.615 s
% 4.53/1.02  % (23911)------------------------------
% 4.53/1.02  % (23911)------------------------------
% 4.53/1.04  % (23932)Time limit reached!
% 4.53/1.04  % (23932)------------------------------
% 4.53/1.04  % (23932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/1.04  % (23932)Termination reason: Time limit
% 4.53/1.04  
% 4.53/1.04  % (23932)Memory used [KB]: 8827
% 4.53/1.04  % (23932)Time elapsed: 0.635 s
% 4.53/1.04  % (23932)------------------------------
% 4.53/1.04  % (23932)------------------------------
% 4.95/1.05  % (23938)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.95/1.06  % (23939)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.95/1.07  % (23940)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.66/1.10  % (23941)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.02/1.14  % (23942)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.28/1.18  % (23943)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.28/1.18  % (23944)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.82/1.24  % (23925)Time limit reached!
% 6.82/1.24  % (23925)------------------------------
% 6.82/1.24  % (23925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.82/1.24  % (23925)Termination reason: Time limit
% 6.82/1.24  % (23925)Termination phase: Saturation
% 6.82/1.24  
% 6.82/1.24  % (23925)Memory used [KB]: 5373
% 6.82/1.24  % (23925)Time elapsed: 0.800 s
% 6.82/1.24  % (23925)------------------------------
% 6.82/1.24  % (23925)------------------------------
% 6.82/1.27  % (23937)Time limit reached!
% 6.82/1.27  % (23937)------------------------------
% 6.82/1.27  % (23937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.82/1.27  % (23937)Termination reason: Time limit
% 6.82/1.27  
% 6.82/1.27  % (23937)Memory used [KB]: 8955
% 6.82/1.27  % (23937)Time elapsed: 0.407 s
% 6.82/1.27  % (23937)------------------------------
% 6.82/1.27  % (23937)------------------------------
% 7.71/1.35  % (23938)Time limit reached!
% 7.71/1.35  % (23938)------------------------------
% 7.71/1.35  % (23938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.71/1.36  % (23938)Termination reason: Time limit
% 7.71/1.36  % (23938)Termination phase: Saturation
% 7.71/1.36  
% 7.71/1.36  % (23938)Memory used [KB]: 13688
% 7.71/1.36  % (23938)Time elapsed: 0.400 s
% 7.71/1.36  % (23938)------------------------------
% 7.71/1.36  % (23938)------------------------------
% 7.90/1.39  % (23946)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.90/1.42  % (23945)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.90/1.42  % (23924)Refutation found. Thanks to Tanya!
% 7.90/1.42  % SZS status Theorem for theBenchmark
% 7.90/1.42  % SZS output start Proof for theBenchmark
% 7.90/1.42  fof(f7102,plain,(
% 7.90/1.42    $false),
% 7.90/1.42    inference(avatar_sat_refutation,[],[f82,f88,f93,f99,f105,f116,f123,f130,f156,f163,f702,f737,f2110,f5443,f5615,f5880,f5892,f6077,f6088,f6095,f6287,f6332,f7101])).
% 7.90/1.42  fof(f7101,plain,(
% 7.90/1.42    ~spl4_2 | ~spl4_8 | ~spl4_78 | spl4_93),
% 7.90/1.42    inference(avatar_contradiction_clause,[],[f7100])).
% 7.90/1.42  fof(f7100,plain,(
% 7.90/1.42    $false | (~spl4_2 | ~spl4_8 | ~spl4_78 | spl4_93)),
% 7.90/1.42    inference(subsumption_resolution,[],[f7099,f6337])).
% 7.90/1.42  fof(f6337,plain,(
% 7.90/1.42    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,sK2))) ) | spl4_93),
% 7.90/1.42    inference(resolution,[],[f6331,f67])).
% 7.90/1.42  fof(f67,plain,(
% 7.90/1.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 7.90/1.42    inference(cnf_transformation,[],[f33])).
% 7.90/1.42  fof(f33,plain,(
% 7.90/1.42    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.90/1.42    inference(ennf_transformation,[],[f3])).
% 7.90/1.42  fof(f3,axiom,(
% 7.90/1.42    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.90/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 7.90/1.42  fof(f6331,plain,(
% 7.90/1.42    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) | spl4_93),
% 7.90/1.42    inference(avatar_component_clause,[],[f6329])).
% 7.90/1.42  fof(f6329,plain,(
% 7.90/1.42    spl4_93 <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)),
% 7.90/1.42    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 7.90/1.42  fof(f7099,plain,(
% 7.90/1.42    r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) | (~spl4_2 | ~spl4_8 | ~spl4_78)),
% 7.90/1.42    inference(subsumption_resolution,[],[f7092,f3915])).
% 7.90/1.42  fof(f3915,plain,(
% 7.90/1.42    ( ! [X41,X42] : (r1_tarski(k4_xboole_0(X42,X42),X41)) ) | (~spl4_2 | ~spl4_8)),
% 7.90/1.42    inference(superposition,[],[f49,f3791])).
% 7.90/1.42  fof(f3791,plain,(
% 7.90/1.42    ( ! [X43,X44] : (k4_xboole_0(X43,X43) = k4_xboole_0(X44,X44)) ) | (~spl4_2 | ~spl4_8)),
% 7.90/1.42    inference(subsumption_resolution,[],[f3775,f3656])).
% 7.90/1.42  fof(f3656,plain,(
% 7.90/1.42    ( ! [X19,X20] : (r1_tarski(k4_xboole_0(X19,X19),k4_xboole_0(X20,X20))) ) | (~spl4_2 | ~spl4_8)),
% 7.90/1.42    inference(resolution,[],[f3635,f3310])).
% 7.90/1.42  fof(f3310,plain,(
% 7.90/1.42    ( ! [X10] : (r1_tarski(k4_xboole_0(X10,X10),u1_struct_0(sK0))) ) | ~spl4_8),
% 7.90/1.42    inference(superposition,[],[f48,f3293])).
% 7.90/1.42  fof(f3293,plain,(
% 7.90/1.42    ( ! [X0] : (u1_struct_0(sK0) = k2_xboole_0(k4_xboole_0(X0,X0),u1_struct_0(sK0))) ) | ~spl4_8),
% 7.90/1.42    inference(resolution,[],[f934,f48])).
% 7.90/1.42  fof(f934,plain,(
% 7.90/1.42    ( ! [X10,X11,X9] : (~r1_tarski(X9,k2_xboole_0(X10,k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),X11)))) | u1_struct_0(sK0) = k2_xboole_0(k4_xboole_0(X9,X10),u1_struct_0(sK0))) ) | ~spl4_8),
% 7.90/1.42    inference(resolution,[],[f438,f65])).
% 7.90/1.42  fof(f65,plain,(
% 7.90/1.42    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.90/1.42    inference(cnf_transformation,[],[f32])).
% 7.90/1.42  fof(f32,plain,(
% 7.90/1.42    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.90/1.42    inference(ennf_transformation,[],[f7])).
% 7.90/1.42  fof(f7,axiom,(
% 7.90/1.42    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.90/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 7.90/1.42  fof(f438,plain,(
% 7.90/1.42    ( ! [X2,X1] : (~r1_tarski(X1,k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),X2))) | u1_struct_0(sK0) = k2_xboole_0(X1,u1_struct_0(sK0))) ) | ~spl4_8),
% 7.90/1.42    inference(resolution,[],[f261,f65])).
% 7.90/1.42  fof(f261,plain,(
% 7.90/1.42    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(X2,sK2),k4_xboole_0(u1_struct_0(sK0),X3)) | u1_struct_0(sK0) = k2_xboole_0(X2,u1_struct_0(sK0))) ) | ~spl4_8),
% 7.90/1.42    inference(resolution,[],[f218,f51])).
% 7.90/1.42  fof(f51,plain,(
% 7.90/1.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 7.90/1.42    inference(cnf_transformation,[],[f27])).
% 7.90/1.42  fof(f27,plain,(
% 7.90/1.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.90/1.42    inference(ennf_transformation,[],[f4])).
% 7.90/1.42  fof(f4,axiom,(
% 7.90/1.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.90/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 7.90/1.42  fof(f218,plain,(
% 7.90/1.42    ( ! [X2,X1] : (r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(k4_xboole_0(X1,sK2),k4_xboole_0(u1_struct_0(sK0),X2))) ) | ~spl4_8),
% 7.90/1.42    inference(resolution,[],[f138,f66])).
% 7.90/1.42  fof(f66,plain,(
% 7.90/1.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 7.90/1.42    inference(cnf_transformation,[],[f33])).
% 7.90/1.42  fof(f138,plain,(
% 7.90/1.42    ( ! [X0] : (~r1_tarski(k4_xboole_0(X0,sK2),u1_struct_0(sK0)) | r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl4_8),
% 7.90/1.42    inference(superposition,[],[f68,f122])).
% 7.90/1.42  fof(f122,plain,(
% 7.90/1.42    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) | ~spl4_8),
% 7.90/1.42    inference(avatar_component_clause,[],[f120])).
% 7.90/1.42  fof(f120,plain,(
% 7.90/1.42    spl4_8 <=> u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))),
% 7.90/1.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 7.90/1.42  fof(f68,plain,(
% 7.90/1.42    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.90/1.42    inference(cnf_transformation,[],[f34])).
% 7.90/1.42  fof(f34,plain,(
% 7.90/1.42    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.90/1.42    inference(ennf_transformation,[],[f8])).
% 7.90/1.42  fof(f8,axiom,(
% 7.90/1.42    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.90/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 7.90/1.42  fof(f48,plain,(
% 7.90/1.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.90/1.42    inference(cnf_transformation,[],[f11])).
% 7.90/1.42  fof(f11,axiom,(
% 7.90/1.42    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.90/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 7.90/1.42  fof(f3635,plain,(
% 7.90/1.42    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(sK0)) | r1_tarski(k4_xboole_0(X1,X1),X0)) ) | ~spl4_2),
% 7.90/1.42    inference(resolution,[],[f1127,f48])).
% 7.90/1.42  fof(f1127,plain,(
% 7.90/1.42    ( ! [X17,X15,X18,X16] : (~r1_tarski(X15,k2_xboole_0(X16,k2_xboole_0(k1_tops_1(sK0,X17),k4_xboole_0(X17,X18)))) | ~r1_tarski(X17,u1_struct_0(sK0)) | r1_tarski(k4_xboole_0(X15,X16),X17)) ) | ~spl4_2),
% 7.90/1.42    inference(resolution,[],[f497,f65])).
% 7.90/1.42  fof(f497,plain,(
% 7.90/1.42    ( ! [X4,X2,X3] : (~r1_tarski(X3,k2_xboole_0(k1_tops_1(sK0,X2),k4_xboole_0(X2,X4))) | r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(sK0))) ) | ~spl4_2),
% 7.90/1.42    inference(resolution,[],[f278,f65])).
% 7.90/1.42  fof(f278,plain,(
% 7.90/1.42    ( ! [X4,X5,X3] : (~r1_tarski(k4_xboole_0(X3,k1_tops_1(sK0,X4)),k4_xboole_0(X4,X5)) | ~r1_tarski(X4,u1_struct_0(sK0)) | r1_tarski(X3,X4)) ) | ~spl4_2),
% 7.90/1.42    inference(resolution,[],[f229,f66])).
% 7.90/1.42  fof(f229,plain,(
% 7.90/1.42    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,k1_tops_1(sK0,X1)),X1) | r1_tarski(X0,X1) | ~r1_tarski(X1,u1_struct_0(sK0))) ) | ~spl4_2),
% 7.90/1.42    inference(resolution,[],[f190,f58])).
% 7.90/1.42  fof(f58,plain,(
% 7.90/1.42    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.90/1.42    inference(cnf_transformation,[],[f15])).
% 7.90/1.42  fof(f15,axiom,(
% 7.90/1.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.90/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 7.90/1.42  fof(f190,plain,(
% 7.90/1.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(X1,k1_tops_1(sK0,X0)),X0) | r1_tarski(X1,X0)) ) | ~spl4_2),
% 7.90/1.42    inference(superposition,[],[f68,f125])).
% 7.90/1.42  fof(f125,plain,(
% 7.90/1.42    ( ! [X1] : (k2_xboole_0(k1_tops_1(sK0,X1),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_2),
% 7.90/1.42    inference(resolution,[],[f83,f51])).
% 7.90/1.42  fof(f83,plain,(
% 7.90/1.42    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_2),
% 7.90/1.42    inference(resolution,[],[f81,f45])).
% 7.90/1.42  fof(f45,plain,(
% 7.90/1.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 7.90/1.42    inference(cnf_transformation,[],[f24])).
% 7.90/1.42  fof(f24,plain,(
% 7.90/1.42    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.90/1.42    inference(ennf_transformation,[],[f18])).
% 7.90/1.42  fof(f18,axiom,(
% 7.90/1.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 7.90/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 7.90/1.43  % (23906)Time limit reached!
% 7.90/1.43  % (23906)------------------------------
% 7.90/1.43  % (23906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.90/1.43  % (23906)Termination reason: Time limit
% 7.90/1.43  
% 7.90/1.43  % (23906)Memory used [KB]: 20596
% 7.90/1.43  % (23906)Time elapsed: 1.004 s
% 7.90/1.43  % (23906)------------------------------
% 7.90/1.43  % (23906)------------------------------
% 8.34/1.44  fof(f81,plain,(
% 8.34/1.44    l1_pre_topc(sK0) | ~spl4_2),
% 8.34/1.44    inference(avatar_component_clause,[],[f79])).
% 8.34/1.44  fof(f79,plain,(
% 8.34/1.44    spl4_2 <=> l1_pre_topc(sK0)),
% 8.34/1.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 8.34/1.44  fof(f3775,plain,(
% 8.34/1.44    ( ! [X43,X44] : (~r1_tarski(k4_xboole_0(X43,X43),k4_xboole_0(X44,X44)) | k4_xboole_0(X43,X43) = k4_xboole_0(X44,X44)) ) | (~spl4_2 | ~spl4_8)),
% 8.34/1.44    inference(resolution,[],[f3656,f54])).
% 8.34/1.44  fof(f54,plain,(
% 8.34/1.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 8.34/1.44    inference(cnf_transformation,[],[f2])).
% 8.34/1.44  fof(f2,axiom,(
% 8.34/1.44    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.34/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 8.34/1.44  fof(f49,plain,(
% 8.34/1.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 8.34/1.44    inference(cnf_transformation,[],[f5])).
% 8.34/1.44  fof(f5,axiom,(
% 8.34/1.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 8.34/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 8.34/1.44  fof(f7092,plain,(
% 8.34/1.44    ( ! [X1] : (~r1_tarski(k4_xboole_0(X1,X1),k4_xboole_0(sK1,sK2)) | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))) ) | (~spl4_2 | ~spl4_8 | ~spl4_78)),
% 8.34/1.44    inference(superposition,[],[f6256,f3791])).
% 8.34/1.44  fof(f6256,plain,(
% 8.34/1.44    ( ! [X8] : (~r1_tarski(k4_xboole_0(X8,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)) | r1_tarski(X8,k4_xboole_0(sK1,sK2))) ) | (~spl4_2 | ~spl4_78)),
% 8.34/1.44    inference(resolution,[],[f5933,f190])).
% 8.34/1.44  fof(f5933,plain,(
% 8.34/1.44    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_78),
% 8.34/1.44    inference(avatar_component_clause,[],[f5932])).
% 8.34/1.44  fof(f5932,plain,(
% 8.34/1.44    spl4_78 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.34/1.44    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 8.34/1.44  fof(f6332,plain,(
% 8.34/1.44    ~spl4_93 | ~spl4_4 | spl4_90),
% 8.34/1.44    inference(avatar_split_clause,[],[f6325,f6284,f90,f6329])).
% 8.34/1.44  fof(f90,plain,(
% 8.34/1.44    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.34/1.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 8.34/1.44  fof(f6284,plain,(
% 8.34/1.44    spl4_90 <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2)),
% 8.34/1.44    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 8.34/1.44  fof(f6325,plain,(
% 8.34/1.44    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) | (~spl4_4 | spl4_90)),
% 8.34/1.44    inference(subsumption_resolution,[],[f6324,f92])).
% 8.34/1.44  fof(f92,plain,(
% 8.34/1.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 8.34/1.44    inference(avatar_component_clause,[],[f90])).
% 8.34/1.44  fof(f6324,plain,(
% 8.34/1.44    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_90),
% 8.34/1.44    inference(superposition,[],[f6286,f64])).
% 8.34/1.44  fof(f64,plain,(
% 8.34/1.44    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.34/1.44    inference(cnf_transformation,[],[f31])).
% 8.34/1.44  fof(f31,plain,(
% 8.34/1.44    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.34/1.44    inference(ennf_transformation,[],[f13])).
% 8.34/1.44  fof(f13,axiom,(
% 8.34/1.44    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 8.34/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 8.34/1.44  fof(f6286,plain,(
% 8.34/1.44    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2) | spl4_90),
% 8.34/1.44    inference(avatar_component_clause,[],[f6284])).
% 8.34/1.44  fof(f6287,plain,(
% 8.34/1.44    ~spl4_90 | ~spl4_2 | ~spl4_3 | spl4_65),
% 8.34/1.44    inference(avatar_split_clause,[],[f6178,f5612,f85,f79,f6284])).
% 8.34/1.44  fof(f85,plain,(
% 8.34/1.44    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.34/1.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 8.34/1.44  fof(f5612,plain,(
% 8.34/1.44    spl4_65 <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))),
% 8.34/1.44    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 8.34/1.44  fof(f6178,plain,(
% 8.34/1.44    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2) | (~spl4_2 | ~spl4_3 | spl4_65)),
% 8.34/1.44    inference(subsumption_resolution,[],[f6174,f87])).
% 8.34/1.44  fof(f87,plain,(
% 8.34/1.44    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 8.34/1.44    inference(avatar_component_clause,[],[f85])).
% 8.34/1.44  fof(f6174,plain,(
% 8.34/1.44    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | spl4_65)),
% 8.34/1.44    inference(superposition,[],[f6113,f125])).
% 8.34/1.44  fof(f6113,plain,(
% 8.34/1.44    ( ! [X1] : (~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_xboole_0(k1_tops_1(sK0,sK2),X1))) ) | spl4_65),
% 8.34/1.44    inference(resolution,[],[f5614,f61])).
% 8.34/1.44  fof(f61,plain,(
% 8.34/1.44    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 8.34/1.44    inference(cnf_transformation,[],[f30])).
% 8.34/1.44  fof(f30,plain,(
% 8.34/1.44    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 8.34/1.44    inference(ennf_transformation,[],[f9])).
% 8.34/1.44  fof(f9,axiom,(
% 8.34/1.44    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 8.34/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 8.34/1.44  fof(f5614,plain,(
% 8.34/1.44    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | spl4_65),
% 8.34/1.44    inference(avatar_component_clause,[],[f5612])).
% 8.34/1.44  fof(f6095,plain,(
% 8.34/1.44    ~spl4_4 | spl4_72 | ~spl4_78),
% 8.34/1.44    inference(avatar_contradiction_clause,[],[f6094])).
% 8.34/1.44  fof(f6094,plain,(
% 8.34/1.44    $false | (~spl4_4 | spl4_72 | ~spl4_78)),
% 8.34/1.44    inference(subsumption_resolution,[],[f5933,f6089])).
% 8.34/1.44  fof(f6089,plain,(
% 8.34/1.44    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | spl4_72)),
% 8.34/1.44    inference(subsumption_resolution,[],[f5908,f92])).
% 8.34/1.44  fof(f5908,plain,(
% 8.34/1.44    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_72),
% 8.34/1.44    inference(superposition,[],[f5879,f64])).
% 8.34/1.44  fof(f5879,plain,(
% 8.34/1.44    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_72),
% 8.34/1.44    inference(avatar_component_clause,[],[f5877])).
% 8.34/1.44  fof(f5877,plain,(
% 8.34/1.44    spl4_72 <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.34/1.44    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 8.34/1.44  fof(f6088,plain,(
% 8.34/1.44    ~spl4_7 | ~spl4_8 | spl4_85),
% 8.34/1.44    inference(avatar_contradiction_clause,[],[f6087])).
% 8.34/1.44  fof(f6087,plain,(
% 8.34/1.44    $false | (~spl4_7 | ~spl4_8 | spl4_85)),
% 8.34/1.44    inference(subsumption_resolution,[],[f6086,f115])).
% 8.34/1.44  fof(f115,plain,(
% 8.34/1.44    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_7),
% 8.34/1.44    inference(avatar_component_clause,[],[f113])).
% 8.34/1.44  fof(f113,plain,(
% 8.34/1.44    spl4_7 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 8.34/1.44    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 8.34/1.44  fof(f6086,plain,(
% 8.34/1.44    ~r1_tarski(sK1,u1_struct_0(sK0)) | (~spl4_8 | spl4_85)),
% 8.34/1.44    inference(forward_demodulation,[],[f6082,f122])).
% 8.34/1.44  fof(f6082,plain,(
% 8.34/1.44    ~r1_tarski(sK1,k2_xboole_0(sK2,u1_struct_0(sK0))) | spl4_85),
% 8.34/1.44    inference(resolution,[],[f6076,f65])).
% 8.34/1.44  fof(f6076,plain,(
% 8.34/1.44    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl4_85),
% 8.34/1.44    inference(avatar_component_clause,[],[f6074])).
% 8.34/1.44  fof(f6074,plain,(
% 8.34/1.44    spl4_85 <=> r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 8.34/1.44    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 8.34/1.44  fof(f6077,plain,(
% 8.34/1.44    ~spl4_85 | spl4_78),
% 8.34/1.44    inference(avatar_split_clause,[],[f5940,f5932,f6074])).
% 8.34/1.44  fof(f5940,plain,(
% 8.34/1.44    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl4_78),
% 8.34/1.44    inference(resolution,[],[f5934,f58])).
% 8.34/1.44  fof(f5934,plain,(
% 8.34/1.44    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_78),
% 8.34/1.44    inference(avatar_component_clause,[],[f5932])).
% 8.34/1.44  fof(f5892,plain,(
% 8.34/1.44    ~spl4_4 | spl4_71),
% 8.34/1.44    inference(avatar_contradiction_clause,[],[f5891])).
% 8.34/1.44  fof(f5891,plain,(
% 8.34/1.44    $false | (~spl4_4 | spl4_71)),
% 8.34/1.44    inference(subsumption_resolution,[],[f5890,f92])).
% 8.34/1.44  fof(f5890,plain,(
% 8.34/1.44    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_71),
% 8.34/1.44    inference(subsumption_resolution,[],[f5889,f49])).
% 8.34/1.44  fof(f5889,plain,(
% 8.34/1.44    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_71),
% 8.34/1.45    inference(superposition,[],[f5875,f64])).
% 8.34/1.45  fof(f5875,plain,(
% 8.34/1.45    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | spl4_71),
% 8.34/1.45    inference(avatar_component_clause,[],[f5873])).
% 8.34/1.45  fof(f5873,plain,(
% 8.34/1.45    spl4_71 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)),
% 8.34/1.45    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 8.34/1.45  fof(f5880,plain,(
% 8.34/1.45    ~spl4_71 | ~spl4_72 | ~spl4_2 | ~spl4_4 | spl4_64),
% 8.34/1.45    inference(avatar_split_clause,[],[f5626,f5608,f90,f79,f5877,f5873])).
% 8.34/1.45  fof(f5608,plain,(
% 8.34/1.45    spl4_64 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))),
% 8.34/1.45    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 8.34/1.45  fof(f5626,plain,(
% 8.34/1.45    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | (~spl4_2 | ~spl4_4 | spl4_64)),
% 8.34/1.45    inference(subsumption_resolution,[],[f5625,f81])).
% 8.34/1.45  fof(f5625,plain,(
% 8.34/1.45    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~l1_pre_topc(sK0) | (~spl4_4 | spl4_64)),
% 8.34/1.45    inference(subsumption_resolution,[],[f5622,f92])).
% 8.34/1.45  fof(f5622,plain,(
% 8.34/1.45    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~l1_pre_topc(sK0) | spl4_64),
% 8.34/1.45    inference(resolution,[],[f5610,f46])).
% 8.34/1.45  fof(f46,plain,(
% 8.34/1.45    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 8.34/1.45    inference(cnf_transformation,[],[f26])).
% 8.34/1.45  fof(f26,plain,(
% 8.34/1.45    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.34/1.45    inference(flattening,[],[f25])).
% 8.34/1.45  fof(f25,plain,(
% 8.34/1.45    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.34/1.45    inference(ennf_transformation,[],[f19])).
% 8.34/1.45  fof(f19,axiom,(
% 8.34/1.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 8.34/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 8.34/1.45  fof(f5610,plain,(
% 8.34/1.45    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | spl4_64),
% 8.34/1.45    inference(avatar_component_clause,[],[f5608])).
% 8.34/1.45  fof(f5615,plain,(
% 8.34/1.45    ~spl4_64 | ~spl4_65 | spl4_12),
% 8.34/1.45    inference(avatar_split_clause,[],[f5570,f153,f5612,f5608])).
% 8.34/1.45  fof(f153,plain,(
% 8.34/1.45    spl4_12 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 8.34/1.45    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 8.34/1.45  fof(f5570,plain,(
% 8.34/1.45    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | spl4_12),
% 8.34/1.45    inference(resolution,[],[f155,f70])).
% 8.34/1.45  fof(f70,plain,(
% 8.34/1.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 8.34/1.45    inference(cnf_transformation,[],[f38])).
% 8.34/1.45  fof(f38,plain,(
% 8.34/1.45    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 8.34/1.45    inference(flattening,[],[f37])).
% 8.34/1.45  fof(f37,plain,(
% 8.34/1.45    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 8.34/1.45    inference(ennf_transformation,[],[f12])).
% 8.34/1.45  fof(f12,axiom,(
% 8.34/1.45    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 8.34/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 8.34/1.45  fof(f155,plain,(
% 8.34/1.45    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl4_12),
% 8.34/1.45    inference(avatar_component_clause,[],[f153])).
% 8.34/1.45  fof(f5443,plain,(
% 8.34/1.45    ~spl4_2 | ~spl4_8 | ~spl4_9 | spl4_13 | ~spl4_30 | ~spl4_54),
% 8.34/1.45    inference(avatar_contradiction_clause,[],[f5442])).
% 8.34/1.45  fof(f5442,plain,(
% 8.34/1.45    $false | (~spl4_2 | ~spl4_8 | ~spl4_9 | spl4_13 | ~spl4_30 | ~spl4_54)),
% 8.34/1.45    inference(subsumption_resolution,[],[f5441,f736])).
% 8.34/1.45  fof(f736,plain,(
% 8.34/1.45    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_30),
% 8.34/1.45    inference(avatar_component_clause,[],[f734])).
% 8.34/1.45  fof(f734,plain,(
% 8.34/1.45    spl4_30 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 8.34/1.45    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 8.34/1.45  fof(f5441,plain,(
% 8.34/1.45    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl4_2 | ~spl4_8 | ~spl4_9 | spl4_13 | ~spl4_54)),
% 8.34/1.45    inference(forward_demodulation,[],[f5440,f2109])).
% 8.34/1.45  fof(f2109,plain,(
% 8.34/1.45    sK1 = k2_xboole_0(sK1,sK1) | ~spl4_54),
% 8.34/1.45    inference(avatar_component_clause,[],[f2107])).
% 8.34/1.45  fof(f2107,plain,(
% 8.34/1.45    spl4_54 <=> sK1 = k2_xboole_0(sK1,sK1)),
% 8.34/1.45    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 8.34/1.45  fof(f5440,plain,(
% 8.34/1.45    ~r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,sK1)) | (~spl4_2 | ~spl4_8 | ~spl4_9 | spl4_13)),
% 8.34/1.45    inference(forward_demodulation,[],[f5001,f3916])).
% 8.34/1.45  fof(f3916,plain,(
% 8.34/1.45    ( ! [X43,X44] : (k2_xboole_0(X43,X43) = k2_xboole_0(X43,k4_xboole_0(X44,X44))) ) | (~spl4_2 | ~spl4_8)),
% 8.34/1.45    inference(superposition,[],[f50,f3791])).
% 8.34/1.45  fof(f50,plain,(
% 8.34/1.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.34/1.45    inference(cnf_transformation,[],[f6])).
% 8.34/1.45  fof(f6,axiom,(
% 8.34/1.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 8.34/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 8.34/1.45  fof(f5001,plain,(
% 8.34/1.45    ( ! [X1341] : (~r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,k4_xboole_0(X1341,X1341)))) ) | (~spl4_2 | ~spl4_8 | ~spl4_9 | spl4_13)),
% 8.34/1.45    inference(superposition,[],[f353,f3791])).
% 8.34/1.45  fof(f353,plain,(
% 8.34/1.45    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0)))) ) | (~spl4_9 | spl4_13)),
% 8.34/1.45    inference(resolution,[],[f271,f65])).
% 8.34/1.45  fof(f271,plain,(
% 8.34/1.45    ( ! [X8] : (~r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),sK1),k4_xboole_0(u1_struct_0(sK0),X8))) ) | (~spl4_9 | spl4_13)),
% 8.34/1.45    inference(resolution,[],[f226,f162])).
% 8.34/1.45  fof(f162,plain,(
% 8.34/1.45    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl4_13),
% 8.34/1.45    inference(avatar_component_clause,[],[f160])).
% 8.34/1.45  fof(f160,plain,(
% 8.34/1.45    spl4_13 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 8.34/1.45    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 8.34/1.45  fof(f226,plain,(
% 8.34/1.45    ( ! [X2,X1] : (r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(k4_xboole_0(X1,sK1),k4_xboole_0(u1_struct_0(sK0),X2))) ) | ~spl4_9),
% 8.34/1.45    inference(resolution,[],[f145,f66])).
% 8.34/1.45  fof(f145,plain,(
% 8.34/1.45    ( ! [X0] : (~r1_tarski(k4_xboole_0(X0,sK1),u1_struct_0(sK0)) | r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl4_9),
% 8.34/1.45    inference(superposition,[],[f68,f129])).
% 8.34/1.45  fof(f129,plain,(
% 8.34/1.45    u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) | ~spl4_9),
% 8.34/1.45    inference(avatar_component_clause,[],[f127])).
% 8.34/1.45  fof(f127,plain,(
% 8.34/1.45    spl4_9 <=> u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))),
% 8.34/1.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 8.34/1.45  fof(f2110,plain,(
% 8.34/1.45    spl4_54 | ~spl4_2 | ~spl4_7 | ~spl4_28),
% 8.34/1.45    inference(avatar_split_clause,[],[f2104,f699,f113,f79,f2107])).
% 8.34/1.45  fof(f699,plain,(
% 8.34/1.45    spl4_28 <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 8.34/1.45    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 8.34/1.45  fof(f2104,plain,(
% 8.34/1.45    sK1 = k2_xboole_0(sK1,sK1) | (~spl4_2 | ~spl4_7 | ~spl4_28)),
% 8.34/1.45    inference(forward_demodulation,[],[f2089,f701])).
% 8.34/1.45  fof(f701,plain,(
% 8.34/1.45    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl4_28),
% 8.34/1.45    inference(avatar_component_clause,[],[f699])).
% 8.34/1.45  fof(f2089,plain,(
% 8.34/1.45    sK1 = k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),sK1),sK1) | (~spl4_2 | ~spl4_7)),
% 8.34/1.45    inference(resolution,[],[f650,f115])).
% 8.34/1.45  fof(f650,plain,(
% 8.34/1.45    ( ! [X2] : (~r1_tarski(X2,u1_struct_0(sK0)) | k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,X2),X2),X2) = X2) ) | ~spl4_2),
% 8.34/1.45    inference(resolution,[],[f427,f51])).
% 8.34/1.45  fof(f427,plain,(
% 8.34/1.45    ( ! [X3] : (r1_tarski(k2_xboole_0(k1_tops_1(sK0,X3),X3),X3) | ~r1_tarski(X3,u1_struct_0(sK0))) ) | ~spl4_2),
% 8.34/1.45    inference(resolution,[],[f277,f72])).
% 8.34/1.45  fof(f72,plain,(
% 8.34/1.45    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.34/1.45    inference(equality_resolution,[],[f52])).
% 8.34/1.45  fof(f52,plain,(
% 8.34/1.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 8.34/1.45    inference(cnf_transformation,[],[f2])).
% 8.34/1.45  fof(f277,plain,(
% 8.34/1.45    ( ! [X2,X1] : (~r1_tarski(X1,k2_xboole_0(k1_tops_1(sK0,X2),X2)) | ~r1_tarski(X2,u1_struct_0(sK0)) | r1_tarski(X1,X2)) ) | ~spl4_2),
% 8.34/1.45    inference(resolution,[],[f229,f65])).
% 8.34/1.45  fof(f737,plain,(
% 8.34/1.45    spl4_30 | ~spl4_28),
% 8.34/1.45    inference(avatar_split_clause,[],[f719,f699,f734])).
% 8.34/1.45  fof(f719,plain,(
% 8.34/1.45    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_28),
% 8.34/1.45    inference(superposition,[],[f48,f701])).
% 8.34/1.45  fof(f702,plain,(
% 8.34/1.45    spl4_28 | ~spl4_2 | ~spl4_7),
% 8.34/1.45    inference(avatar_split_clause,[],[f673,f113,f79,f699])).
% 8.34/1.45  fof(f673,plain,(
% 8.34/1.45    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | (~spl4_2 | ~spl4_7)),
% 8.34/1.45    inference(resolution,[],[f435,f115])).
% 8.34/1.45  fof(f435,plain,(
% 8.34/1.45    ( ! [X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | k2_xboole_0(k1_tops_1(sK0,X1),X1) = X1) ) | ~spl4_2),
% 8.34/1.45    inference(resolution,[],[f425,f51])).
% 8.34/1.45  fof(f425,plain,(
% 8.34/1.45    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,X0),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl4_2),
% 8.34/1.45    inference(resolution,[],[f277,f48])).
% 8.34/1.45  fof(f163,plain,(
% 8.34/1.45    ~spl4_13 | spl4_11),
% 8.34/1.45    inference(avatar_split_clause,[],[f157,f149,f160])).
% 8.34/1.45  fof(f149,plain,(
% 8.34/1.45    spl4_11 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.34/1.45    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 8.34/1.45  fof(f157,plain,(
% 8.34/1.45    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl4_11),
% 8.34/1.45    inference(resolution,[],[f151,f58])).
% 8.34/1.45  fof(f151,plain,(
% 8.34/1.45    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_11),
% 8.34/1.45    inference(avatar_component_clause,[],[f149])).
% 8.34/1.45  fof(f156,plain,(
% 8.34/1.45    ~spl4_11 | ~spl4_12 | spl4_6),
% 8.34/1.45    inference(avatar_split_clause,[],[f110,f102,f153,f149])).
% 8.34/1.45  fof(f102,plain,(
% 8.34/1.45    spl4_6 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 8.34/1.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 8.34/1.45  fof(f110,plain,(
% 8.34/1.45    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_6),
% 8.34/1.45    inference(superposition,[],[f104,f64])).
% 8.34/1.45  fof(f104,plain,(
% 8.34/1.45    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl4_6),
% 8.34/1.45    inference(avatar_component_clause,[],[f102])).
% 8.34/1.45  fof(f130,plain,(
% 8.34/1.45    spl4_9 | ~spl4_7),
% 8.34/1.45    inference(avatar_split_clause,[],[f118,f113,f127])).
% 8.34/1.45  fof(f118,plain,(
% 8.34/1.45    u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) | ~spl4_7),
% 8.34/1.45    inference(resolution,[],[f115,f51])).
% 8.34/1.45  fof(f123,plain,(
% 8.34/1.45    spl4_8 | ~spl4_5),
% 8.34/1.45    inference(avatar_split_clause,[],[f107,f96,f120])).
% 8.34/1.45  fof(f96,plain,(
% 8.34/1.45    spl4_5 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 8.34/1.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 8.34/1.45  fof(f107,plain,(
% 8.34/1.45    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) | ~spl4_5),
% 8.34/1.45    inference(resolution,[],[f98,f51])).
% 8.34/1.45  fof(f98,plain,(
% 8.34/1.45    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl4_5),
% 8.34/1.45    inference(avatar_component_clause,[],[f96])).
% 8.34/1.45  fof(f116,plain,(
% 8.34/1.45    spl4_7 | ~spl4_4),
% 8.34/1.45    inference(avatar_split_clause,[],[f100,f90,f113])).
% 8.34/1.45  fof(f100,plain,(
% 8.34/1.45    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 8.34/1.45    inference(resolution,[],[f92,f59])).
% 8.34/1.45  fof(f59,plain,(
% 8.34/1.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 8.34/1.45    inference(cnf_transformation,[],[f15])).
% 8.34/1.45  fof(f105,plain,(
% 8.34/1.45    ~spl4_6),
% 8.34/1.45    inference(avatar_split_clause,[],[f40,f102])).
% 8.34/1.45  fof(f40,plain,(
% 8.34/1.45    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 8.34/1.45    inference(cnf_transformation,[],[f23])).
% 8.34/1.45  fof(f23,plain,(
% 8.34/1.45    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.34/1.45    inference(flattening,[],[f22])).
% 8.34/1.45  fof(f22,plain,(
% 8.34/1.45    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 8.34/1.45    inference(ennf_transformation,[],[f21])).
% 8.34/1.45  fof(f21,negated_conjecture,(
% 8.34/1.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 8.34/1.45    inference(negated_conjecture,[],[f20])).
% 8.34/1.45  fof(f20,conjecture,(
% 8.34/1.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 8.34/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).
% 8.34/1.45  fof(f99,plain,(
% 8.34/1.45    spl4_5 | ~spl4_3),
% 8.34/1.45    inference(avatar_split_clause,[],[f94,f85,f96])).
% 8.34/1.45  fof(f94,plain,(
% 8.34/1.45    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl4_3),
% 8.34/1.45    inference(resolution,[],[f87,f59])).
% 8.34/1.45  fof(f93,plain,(
% 8.34/1.45    spl4_4),
% 8.34/1.45    inference(avatar_split_clause,[],[f41,f90])).
% 8.34/1.45  fof(f41,plain,(
% 8.34/1.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.34/1.45    inference(cnf_transformation,[],[f23])).
% 8.34/1.45  fof(f88,plain,(
% 8.34/1.45    spl4_3),
% 8.34/1.45    inference(avatar_split_clause,[],[f39,f85])).
% 8.34/1.45  fof(f39,plain,(
% 8.34/1.45    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.34/1.45    inference(cnf_transformation,[],[f23])).
% 8.34/1.45  fof(f82,plain,(
% 8.34/1.45    spl4_2),
% 8.34/1.45    inference(avatar_split_clause,[],[f43,f79])).
% 8.34/1.45  fof(f43,plain,(
% 8.34/1.45    l1_pre_topc(sK0)),
% 8.34/1.45    inference(cnf_transformation,[],[f23])).
% 8.34/1.45  % SZS output end Proof for theBenchmark
% 8.34/1.45  % (23924)------------------------------
% 8.34/1.45  % (23924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.34/1.45  % (23924)Termination reason: Refutation
% 8.34/1.45  
% 8.34/1.45  % (23924)Memory used [KB]: 16886
% 8.34/1.45  % (23924)Time elapsed: 1.018 s
% 8.34/1.45  % (23924)------------------------------
% 8.34/1.45  % (23924)------------------------------
% 8.34/1.45  % (23903)Success in time 1.096 s
%------------------------------------------------------------------------------
