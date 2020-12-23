%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:23 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 122 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  236 ( 338 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f109,f114,f119,f153,f237,f252,f275,f291])).

fof(f291,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(subsumption_resolution,[],[f289,f113])).

fof(f113,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f289,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(subsumption_resolution,[],[f287,f96])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f287,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(resolution,[],[f274,f142])).

fof(f142,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK0,X0),sK1)
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f141,f113])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | r1_tarski(k2_pre_topc(sK0,X0),sK1) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f102,f108])).

fof(f108,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_2
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0)
        | r1_tarski(k2_pre_topc(sK0,X1),X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f100,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_pre_topc(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

fof(f100,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f274,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl3_13
  <=> r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f275,plain,
    ( ~ spl3_13
    | spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f260,f249,f116,f272])).

fof(f116,plain,
    ( spl3_4
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f249,plain,
    ( spl3_10
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f260,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | spl3_4
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f255,f68])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f255,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ r1_tarski(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | spl3_4
    | ~ spl3_10 ),
    inference(superposition,[],[f127,f251])).

fof(f251,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f249])).

fof(f127,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(k2_xboole_0(X1,X2),sK1)
        | ~ r1_tarski(k4_xboole_0(k2_tops_1(sK0,sK1),X1),X2) )
    | spl3_4 ),
    inference(resolution,[],[f122,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_tops_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl3_4 ),
    inference(superposition,[],[f120,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f120,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k2_tops_1(sK0,sK1),X0),sK1)
    | spl3_4 ),
    inference(resolution,[],[f118,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f118,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f252,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f239,f226,f150,f111,f249])).

fof(f150,plain,
    ( spl3_5
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f226,plain,
    ( spl3_8
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f239,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f160,f227])).

fof(f227,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f226])).

fof(f160,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f156,f113])).

fof(f156,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f152,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f152,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f237,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | spl3_8 ),
    inference(subsumption_resolution,[],[f235,f100])).

fof(f235,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_8 ),
    inference(subsumption_resolution,[],[f234,f113])).

fof(f234,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_8 ),
    inference(resolution,[],[f228,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f228,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f226])).

fof(f153,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f132,f111,f98,f150])).

fof(f132,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f103,f113])).

fof(f103,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X2) = k4_subset_1(u1_struct_0(sK0),X2,k2_tops_1(sK0,X2)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f100,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f119,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f59,f116])).

fof(f59,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f114,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f57,f111])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f109,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f58,f106])).

fof(f58,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f101,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f60,f98])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:48:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (10373)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (10376)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.17/0.52  % (10389)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.17/0.52  % (10384)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.17/0.52  % (10380)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.17/0.53  % (10372)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.17/0.53  % (10379)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.17/0.53  % (10378)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.17/0.53  % (10383)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.17/0.53  % (10386)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.17/0.53  % (10394)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.17/0.53  % (10392)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.17/0.53  % (10395)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.17/0.53  % (10381)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.17/0.54  % (10393)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.17/0.54  % (10388)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.17/0.54  % (10387)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.54  % (10387)Refutation not found, incomplete strategy% (10387)------------------------------
% 1.31/0.54  % (10387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (10387)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (10387)Memory used [KB]: 10746
% 1.31/0.54  % (10387)Time elapsed: 0.116 s
% 1.31/0.54  % (10387)------------------------------
% 1.31/0.54  % (10387)------------------------------
% 1.31/0.54  % (10371)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (10398)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.54  % (10385)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.54  % (10396)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.54  % (10375)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.55  % (10374)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.55  % (10391)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.55  % (10399)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.55  % (10382)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.55  % (10370)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.56  % (10377)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.56  % (10390)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.56  % (10397)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.57  % (10390)Refutation found. Thanks to Tanya!
% 1.31/0.57  % SZS status Theorem for theBenchmark
% 1.31/0.57  % SZS output start Proof for theBenchmark
% 1.31/0.57  fof(f292,plain,(
% 1.31/0.57    $false),
% 1.31/0.57    inference(avatar_sat_refutation,[],[f101,f109,f114,f119,f153,f237,f252,f275,f291])).
% 1.31/0.57  fof(f291,plain,(
% 1.31/0.57    ~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_13),
% 1.31/0.57    inference(avatar_contradiction_clause,[],[f290])).
% 1.31/0.57  fof(f290,plain,(
% 1.31/0.57    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_13)),
% 1.31/0.57    inference(subsumption_resolution,[],[f289,f113])).
% 1.31/0.57  fof(f113,plain,(
% 1.31/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 1.31/0.57    inference(avatar_component_clause,[],[f111])).
% 1.31/0.57  fof(f111,plain,(
% 1.31/0.57    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.31/0.57  fof(f289,plain,(
% 1.31/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_13)),
% 1.31/0.57    inference(subsumption_resolution,[],[f287,f96])).
% 1.31/0.57  fof(f96,plain,(
% 1.31/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.57    inference(equality_resolution,[],[f84])).
% 1.31/0.57  fof(f84,plain,(
% 1.31/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.31/0.57    inference(cnf_transformation,[],[f2])).
% 1.31/0.57  fof(f2,axiom,(
% 1.31/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.57  fof(f287,plain,(
% 1.31/0.57    ~r1_tarski(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_13)),
% 1.31/0.57    inference(resolution,[],[f274,f142])).
% 1.31/0.57  fof(f142,plain,(
% 1.31/0.57    ( ! [X0] : (r1_tarski(k2_pre_topc(sK0,X0),sK1) | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 1.31/0.57    inference(subsumption_resolution,[],[f141,f113])).
% 1.31/0.57  fof(f141,plain,(
% 1.31/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | r1_tarski(k2_pre_topc(sK0,X0),sK1)) ) | (~spl3_1 | ~spl3_2)),
% 1.31/0.57    inference(resolution,[],[f102,f108])).
% 1.31/0.57  fof(f108,plain,(
% 1.31/0.57    v4_pre_topc(sK1,sK0) | ~spl3_2),
% 1.31/0.57    inference(avatar_component_clause,[],[f106])).
% 1.31/0.57  fof(f106,plain,(
% 1.31/0.57    spl3_2 <=> v4_pre_topc(sK1,sK0)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.31/0.57  fof(f102,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | r1_tarski(k2_pre_topc(sK0,X1),X0)) ) | ~spl3_1),
% 1.31/0.57    inference(resolution,[],[f100,f65])).
% 1.31/0.57  fof(f65,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~r1_tarski(X2,X1) | r1_tarski(k2_pre_topc(X0,X2),X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f38])).
% 1.31/0.57  fof(f38,plain,(
% 1.31/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.57    inference(flattening,[],[f37])).
% 1.31/0.57  fof(f37,plain,(
% 1.31/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.57    inference(ennf_transformation,[],[f28])).
% 1.31/0.57  fof(f28,axiom,(
% 1.31/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 1.31/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).
% 1.31/0.57  fof(f100,plain,(
% 1.31/0.57    l1_pre_topc(sK0) | ~spl3_1),
% 1.31/0.57    inference(avatar_component_clause,[],[f98])).
% 1.31/0.57  fof(f98,plain,(
% 1.31/0.57    spl3_1 <=> l1_pre_topc(sK0)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.31/0.57  fof(f274,plain,(
% 1.31/0.57    ~r1_tarski(k2_pre_topc(sK0,sK1),sK1) | spl3_13),
% 1.31/0.57    inference(avatar_component_clause,[],[f272])).
% 1.31/0.57  fof(f272,plain,(
% 1.31/0.57    spl3_13 <=> r1_tarski(k2_pre_topc(sK0,sK1),sK1)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.31/0.59  fof(f275,plain,(
% 1.31/0.59    ~spl3_13 | spl3_4 | ~spl3_10),
% 1.31/0.59    inference(avatar_split_clause,[],[f260,f249,f116,f272])).
% 1.31/0.59  fof(f116,plain,(
% 1.31/0.59    spl3_4 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.31/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.31/0.59  fof(f249,plain,(
% 1.31/0.59    spl3_10 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.31/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.31/0.59  fof(f260,plain,(
% 1.31/0.59    ~r1_tarski(k2_pre_topc(sK0,sK1),sK1) | (spl3_4 | ~spl3_10)),
% 1.31/0.59    inference(subsumption_resolution,[],[f255,f68])).
% 1.31/0.59  fof(f68,plain,(
% 1.31/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.31/0.59    inference(cnf_transformation,[],[f8])).
% 1.31/0.59  fof(f8,axiom,(
% 1.31/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.31/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.31/0.59  fof(f255,plain,(
% 1.31/0.59    ~r1_tarski(k2_pre_topc(sK0,sK1),sK1) | ~r1_tarski(k4_xboole_0(k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | (spl3_4 | ~spl3_10)),
% 1.31/0.59    inference(superposition,[],[f127,f251])).
% 1.31/0.59  fof(f251,plain,(
% 1.31/0.59    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_10),
% 1.31/0.59    inference(avatar_component_clause,[],[f249])).
% 1.31/0.59  fof(f127,plain,(
% 1.31/0.59    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),sK1) | ~r1_tarski(k4_xboole_0(k2_tops_1(sK0,sK1),X1),X2)) ) | spl3_4),
% 1.31/0.59    inference(resolution,[],[f122,f92])).
% 1.31/0.59  fof(f92,plain,(
% 1.31/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.31/0.59    inference(cnf_transformation,[],[f52])).
% 1.31/0.59  fof(f52,plain,(
% 1.31/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.31/0.59    inference(ennf_transformation,[],[f12])).
% 1.31/0.59  fof(f12,axiom,(
% 1.31/0.59    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.31/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.31/0.59  fof(f122,plain,(
% 1.31/0.59    ( ! [X0] : (~r1_tarski(k2_tops_1(sK0,sK1),X0) | ~r1_tarski(X0,sK1)) ) | spl3_4),
% 1.31/0.59    inference(superposition,[],[f120,f76])).
% 1.31/0.59  fof(f76,plain,(
% 1.31/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.31/0.59    inference(cnf_transformation,[],[f39])).
% 1.31/0.59  fof(f39,plain,(
% 1.31/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.31/0.59    inference(ennf_transformation,[],[f5])).
% 1.31/0.59  fof(f5,axiom,(
% 1.31/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.31/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.31/0.59  fof(f120,plain,(
% 1.31/0.59    ( ! [X0] : (~r1_tarski(k2_xboole_0(k2_tops_1(sK0,sK1),X0),sK1)) ) | spl3_4),
% 1.31/0.59    inference(resolution,[],[f118,f91])).
% 1.31/0.59  fof(f91,plain,(
% 1.31/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.31/0.59    inference(cnf_transformation,[],[f51])).
% 1.31/0.59  fof(f51,plain,(
% 1.31/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.31/0.59    inference(ennf_transformation,[],[f4])).
% 1.31/0.59  fof(f4,axiom,(
% 1.31/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.31/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.31/0.59  fof(f118,plain,(
% 1.31/0.59    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl3_4),
% 1.31/0.59    inference(avatar_component_clause,[],[f116])).
% 1.31/0.59  fof(f252,plain,(
% 1.31/0.59    spl3_10 | ~spl3_3 | ~spl3_5 | ~spl3_8),
% 1.31/0.59    inference(avatar_split_clause,[],[f239,f226,f150,f111,f249])).
% 1.31/0.59  fof(f150,plain,(
% 1.31/0.59    spl3_5 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.31/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.31/0.59  fof(f226,plain,(
% 1.31/0.59    spl3_8 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.31/0.59  fof(f239,plain,(
% 1.31/0.59    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_5 | ~spl3_8)),
% 1.31/0.59    inference(subsumption_resolution,[],[f160,f227])).
% 1.31/0.59  fof(f227,plain,(
% 1.31/0.59    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_8),
% 1.31/0.59    inference(avatar_component_clause,[],[f226])).
% 1.31/0.59  fof(f160,plain,(
% 1.31/0.59    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_5)),
% 1.31/0.59    inference(subsumption_resolution,[],[f156,f113])).
% 1.31/0.59  fof(f156,plain,(
% 1.31/0.59    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 1.31/0.59    inference(superposition,[],[f152,f94])).
% 1.31/0.59  fof(f94,plain,(
% 1.31/0.59    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.31/0.59    inference(cnf_transformation,[],[f56])).
% 1.31/0.59  fof(f56,plain,(
% 1.31/0.59    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.59    inference(flattening,[],[f55])).
% 1.31/0.59  fof(f55,plain,(
% 1.31/0.59    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.31/0.59    inference(ennf_transformation,[],[f22])).
% 1.31/0.59  fof(f22,axiom,(
% 1.31/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.31/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.31/0.59  fof(f152,plain,(
% 1.31/0.59    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_5),
% 1.31/0.59    inference(avatar_component_clause,[],[f150])).
% 1.31/0.59  fof(f237,plain,(
% 1.31/0.59    ~spl3_1 | ~spl3_3 | spl3_8),
% 1.31/0.59    inference(avatar_contradiction_clause,[],[f236])).
% 1.31/0.59  fof(f236,plain,(
% 1.31/0.59    $false | (~spl3_1 | ~spl3_3 | spl3_8)),
% 1.31/0.59    inference(subsumption_resolution,[],[f235,f100])).
% 1.31/0.59  fof(f235,plain,(
% 1.31/0.59    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_8)),
% 1.31/0.59    inference(subsumption_resolution,[],[f234,f113])).
% 1.31/0.59  fof(f234,plain,(
% 1.31/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_8),
% 1.31/0.59    inference(resolution,[],[f228,f83])).
% 1.31/0.59  fof(f83,plain,(
% 1.31/0.59    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.31/0.59    inference(cnf_transformation,[],[f48])).
% 1.31/0.59  fof(f48,plain,(
% 1.31/0.59    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.31/0.59    inference(flattening,[],[f47])).
% 1.31/0.59  fof(f47,plain,(
% 1.31/0.59    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.31/0.59    inference(ennf_transformation,[],[f27])).
% 1.31/0.59  fof(f27,axiom,(
% 1.31/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.31/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.31/0.59  fof(f228,plain,(
% 1.31/0.59    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_8),
% 1.31/0.59    inference(avatar_component_clause,[],[f226])).
% 1.31/0.59  fof(f153,plain,(
% 1.31/0.59    spl3_5 | ~spl3_1 | ~spl3_3),
% 1.31/0.59    inference(avatar_split_clause,[],[f132,f111,f98,f150])).
% 1.31/0.59  fof(f132,plain,(
% 1.31/0.59    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl3_1 | ~spl3_3)),
% 1.31/0.59    inference(resolution,[],[f103,f113])).
% 1.31/0.59  fof(f103,plain,(
% 1.31/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X2) = k4_subset_1(u1_struct_0(sK0),X2,k2_tops_1(sK0,X2))) ) | ~spl3_1),
% 1.31/0.59    inference(resolution,[],[f100,f64])).
% 1.31/0.59  fof(f64,plain,(
% 1.31/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.31/0.59    inference(cnf_transformation,[],[f36])).
% 1.31/0.59  fof(f36,plain,(
% 1.31/0.59    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.31/0.59    inference(ennf_transformation,[],[f30])).
% 1.31/0.59  fof(f30,axiom,(
% 1.31/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.31/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.31/0.59  fof(f119,plain,(
% 1.31/0.59    ~spl3_4),
% 1.31/0.59    inference(avatar_split_clause,[],[f59,f116])).
% 1.31/0.59  fof(f59,plain,(
% 1.31/0.59    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.31/0.59    inference(cnf_transformation,[],[f34])).
% 1.31/0.59  fof(f34,plain,(
% 1.31/0.59    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.31/0.59    inference(flattening,[],[f33])).
% 1.31/0.59  fof(f33,plain,(
% 1.31/0.59    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.31/0.59    inference(ennf_transformation,[],[f32])).
% 1.31/0.59  fof(f32,negated_conjecture,(
% 1.31/0.59    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 1.31/0.59    inference(negated_conjecture,[],[f31])).
% 1.31/0.59  fof(f31,conjecture,(
% 1.31/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 1.31/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 1.31/0.59  fof(f114,plain,(
% 1.31/0.59    spl3_3),
% 1.31/0.59    inference(avatar_split_clause,[],[f57,f111])).
% 1.31/0.59  fof(f57,plain,(
% 1.31/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.59    inference(cnf_transformation,[],[f34])).
% 1.31/0.59  fof(f109,plain,(
% 1.31/0.59    spl3_2),
% 1.31/0.59    inference(avatar_split_clause,[],[f58,f106])).
% 1.31/0.59  fof(f58,plain,(
% 1.31/0.59    v4_pre_topc(sK1,sK0)),
% 1.31/0.59    inference(cnf_transformation,[],[f34])).
% 1.31/0.59  fof(f101,plain,(
% 1.31/0.59    spl3_1),
% 1.31/0.59    inference(avatar_split_clause,[],[f60,f98])).
% 1.31/0.59  fof(f60,plain,(
% 1.31/0.59    l1_pre_topc(sK0)),
% 1.31/0.59    inference(cnf_transformation,[],[f34])).
% 1.31/0.59  % SZS output end Proof for theBenchmark
% 1.31/0.59  % (10390)------------------------------
% 1.31/0.59  % (10390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.59  % (10390)Termination reason: Refutation
% 1.31/0.59  
% 1.31/0.59  % (10390)Memory used [KB]: 11001
% 1.31/0.59  % (10390)Time elapsed: 0.144 s
% 1.31/0.59  % (10390)------------------------------
% 1.31/0.59  % (10390)------------------------------
% 1.31/0.59  % (10369)Success in time 0.219 s
%------------------------------------------------------------------------------
