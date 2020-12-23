%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:43 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 267 expanded)
%              Number of leaves         :   20 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  289 ( 744 expanded)
%              Number of equality atoms :   63 ( 205 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f757,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f90,f97,f147,f163,f172,f379,f381,f403,f609,f741,f755])).

fof(f755,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f749])).

fof(f749,plain,
    ( $false
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f29,f28,f27,f96])).

fof(f96,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_4
  <=> ! [X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f741,plain,
    ( ~ spl4_7
    | ~ spl4_18
    | spl4_11
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f721,f170,f174,f370,f150])).

fof(f150,plain,
    ( spl4_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f370,plain,
    ( spl4_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f174,plain,
    ( spl4_11
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f170,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f721,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_10 ),
    inference(duplicate_literal_removal,[],[f720])).

fof(f720,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_10 ),
    inference(superposition,[],[f31,f703])).

fof(f703,plain,
    ( ! [X0] :
        ( sK1 = k7_subset_1(X0,sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f685,f470])).

fof(f470,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f56,f457])).

fof(f457,plain,(
    ! [X12] : k1_xboole_0 = k1_setfam_1(k2_tarski(X12,k1_xboole_0)) ),
    inference(resolution,[],[f449,f105])).

fof(f105,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f74,f56])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f47,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f449,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X1 ) ),
    inference(factoring,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f51,f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f30,f55])).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f685,plain,
    ( ! [X0] :
        ( k7_subset_1(X0,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl4_10 ),
    inference(superposition,[],[f58,f668])).

fof(f668,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(duplicate_literal_removal,[],[f667])).

fof(f667,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(resolution,[],[f574,f488])).

fof(f488,plain,(
    ! [X17,X16] :
      ( r2_hidden(sK3(X16,X17,k1_xboole_0),X16)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X16,X17)) ) ),
    inference(resolution,[],[f69,f105])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f50,f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f574,plain,
    ( ! [X28] :
        ( ~ r2_hidden(sK3(X28,k2_tops_1(sK0,sK1),k1_xboole_0),sK1)
        | k1_xboole_0 = k1_setfam_1(k2_tarski(X28,k2_tops_1(sK0,sK1))) )
    | ~ spl4_10 ),
    inference(resolution,[],[f439,f171])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f439,plain,(
    ! [X17,X16] :
      ( r2_hidden(sK3(X16,X17,k1_xboole_0),X17)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X16,X17)) ) ),
    inference(resolution,[],[f68,f105])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f55])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f609,plain,
    ( ~ spl4_7
    | ~ spl4_18
    | spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f597,f174,f86,f370,f150])).

fof(f86,plain,
    ( spl4_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f597,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_11 ),
    inference(superposition,[],[f32,f176])).

fof(f176,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f403,plain,
    ( ~ spl4_7
    | ~ spl4_1
    | spl4_11
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f383,f92,f174,f82,f150])).

fof(f82,plain,
    ( spl4_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f92,plain,
    ( spl4_3
  <=> ! [X1,X3] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f383,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f27,f93])).

fof(f93,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f381,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f27,f372])).

fof(f372,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f370])).

fof(f379,plain,
    ( spl4_1
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | spl4_1
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f28,f29,f176,f27,f84,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X1,X0) != X0
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(X0,X1) ) ),
    inference(condensation,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) != X1
      | v3_pre_topc(X1,X0) ) ),
    inference(condensation,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k1_tops_1(X0,X2) != X2
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f84,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f172,plain,
    ( ~ spl4_5
    | spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f164,f86,f170,f138])).

fof(f138,plain,
    ( spl4_5
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2 ),
    inference(superposition,[],[f124,f87])).

fof(f87,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f124,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(X13,k7_subset_1(X12,X10,X11))
      | ~ r2_hidden(X13,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X12)) ) ),
    inference(superposition,[],[f74,f58])).

fof(f163,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f29,f152])).

fof(f152,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f150])).

fof(f147,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f29,f27,f140,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f140,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f97,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f34,f95,f92])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f25,f86,f82])).

fof(f25,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f26,f86,f82])).

fof(f26,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:34 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.48  % (13407)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.48  % (13399)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.49  % (13407)Refutation not found, incomplete strategy% (13407)------------------------------
% 0.21/0.49  % (13407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13407)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13407)Memory used [KB]: 10746
% 0.21/0.50  % (13407)Time elapsed: 0.071 s
% 0.21/0.50  % (13407)------------------------------
% 0.21/0.50  % (13407)------------------------------
% 0.21/0.52  % (13381)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (13380)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (13397)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (13385)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (13388)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (13387)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (13392)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (13379)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (13390)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (13403)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (13389)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (13393)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (13382)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (13408)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (13394)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (13408)Refutation not found, incomplete strategy% (13408)------------------------------
% 0.21/0.54  % (13408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13408)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13408)Memory used [KB]: 1663
% 0.21/0.54  % (13408)Time elapsed: 0.001 s
% 0.21/0.54  % (13408)------------------------------
% 0.21/0.54  % (13408)------------------------------
% 0.21/0.54  % (13391)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (13383)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (13395)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (13404)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (13395)Refutation not found, incomplete strategy% (13395)------------------------------
% 0.21/0.54  % (13395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13395)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13395)Memory used [KB]: 10618
% 0.21/0.54  % (13395)Time elapsed: 0.138 s
% 0.21/0.54  % (13395)------------------------------
% 0.21/0.54  % (13395)------------------------------
% 0.21/0.54  % (13400)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (13402)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (13405)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (13396)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (13406)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (13401)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (13389)Refutation not found, incomplete strategy% (13389)------------------------------
% 0.21/0.55  % (13389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13389)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13389)Memory used [KB]: 10746
% 0.21/0.55  % (13389)Time elapsed: 0.153 s
% 0.21/0.55  % (13389)------------------------------
% 0.21/0.55  % (13389)------------------------------
% 0.21/0.55  % (13384)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (13398)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.51/0.56  % (13386)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.51/0.57  % (13452)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.62/0.58  % (13392)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.58  fof(f757,plain,(
% 1.62/0.58    $false),
% 1.62/0.58    inference(avatar_sat_refutation,[],[f89,f90,f97,f147,f163,f172,f379,f381,f403,f609,f741,f755])).
% 1.62/0.58  fof(f755,plain,(
% 1.62/0.58    ~spl4_4),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f749])).
% 1.62/0.58  fof(f749,plain,(
% 1.62/0.58    $false | ~spl4_4),
% 1.62/0.58    inference(unit_resulting_resolution,[],[f29,f28,f27,f96])).
% 1.62/0.58  fof(f96,plain,(
% 1.62/0.58    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl4_4),
% 1.62/0.58    inference(avatar_component_clause,[],[f95])).
% 1.62/0.58  fof(f95,plain,(
% 1.62/0.58    spl4_4 <=> ! [X0,X2] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.58    inference(cnf_transformation,[],[f16])).
% 1.62/0.58  fof(f16,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.62/0.58    inference(flattening,[],[f15])).
% 1.62/0.58  fof(f15,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f14])).
% 1.62/0.58  fof(f14,negated_conjecture,(
% 1.62/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.62/0.58    inference(negated_conjecture,[],[f13])).
% 1.62/0.58  fof(f13,conjecture,(
% 1.62/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 1.62/0.58  fof(f28,plain,(
% 1.62/0.58    v2_pre_topc(sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f16])).
% 1.62/0.58  fof(f29,plain,(
% 1.62/0.58    l1_pre_topc(sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f16])).
% 1.62/0.58  fof(f741,plain,(
% 1.62/0.58    ~spl4_7 | ~spl4_18 | spl4_11 | ~spl4_10),
% 1.62/0.58    inference(avatar_split_clause,[],[f721,f170,f174,f370,f150])).
% 1.62/0.58  fof(f150,plain,(
% 1.62/0.58    spl4_7 <=> l1_pre_topc(sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.62/0.58  fof(f370,plain,(
% 1.62/0.58    spl4_18 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.62/0.58  fof(f174,plain,(
% 1.62/0.58    spl4_11 <=> sK1 = k1_tops_1(sK0,sK1)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.62/0.58  fof(f170,plain,(
% 1.62/0.58    spl4_10 <=> ! [X0] : (~r2_hidden(X0,k2_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.62/0.58  fof(f721,plain,(
% 1.62/0.58    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_10),
% 1.62/0.58    inference(duplicate_literal_removal,[],[f720])).
% 1.62/0.58  fof(f720,plain,(
% 1.62/0.58    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_10),
% 1.62/0.58    inference(superposition,[],[f31,f703])).
% 1.62/0.58  fof(f703,plain,(
% 1.62/0.58    ( ! [X0] : (sK1 = k7_subset_1(X0,sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | ~spl4_10),
% 1.62/0.58    inference(forward_demodulation,[],[f685,f470])).
% 1.62/0.58  fof(f470,plain,(
% 1.62/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.62/0.58    inference(superposition,[],[f56,f457])).
% 1.62/0.59  fof(f457,plain,(
% 1.62/0.59    ( ! [X12] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X12,k1_xboole_0))) )),
% 1.62/0.59    inference(resolution,[],[f449,f105])).
% 1.62/0.59  fof(f105,plain,(
% 1.62/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.62/0.59    inference(condensation,[],[f104])).
% 1.62/0.59  fof(f104,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.62/0.59    inference(superposition,[],[f74,f56])).
% 1.62/0.59  fof(f74,plain,(
% 1.62/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | ~r2_hidden(X3,X1)) )),
% 1.62/0.59    inference(equality_resolution,[],[f60])).
% 1.62/0.59  fof(f60,plain,(
% 1.62/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 1.62/0.59    inference(definition_unfolding,[],[f47,f55])).
% 1.62/0.59  fof(f55,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.62/0.59    inference(definition_unfolding,[],[f36,f35])).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f8])).
% 1.62/0.59  fof(f8,axiom,(
% 1.62/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.62/0.59  fof(f36,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f4])).
% 1.62/0.59  fof(f4,axiom,(
% 1.62/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.62/0.59  fof(f47,plain,(
% 1.62/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.62/0.59    inference(cnf_transformation,[],[f2])).
% 1.62/0.59  fof(f2,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.62/0.59  fof(f449,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | k1_setfam_1(k2_tarski(X0,X1)) = X1) )),
% 1.62/0.59    inference(factoring,[],[f68])).
% 1.62/0.59  fof(f68,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 1.62/0.59    inference(definition_unfolding,[],[f51,f35])).
% 1.62/0.59  fof(f51,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.62/0.59    inference(cnf_transformation,[],[f1])).
% 1.62/0.59  fof(f1,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.62/0.59  fof(f56,plain,(
% 1.62/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 1.62/0.59    inference(definition_unfolding,[],[f30,f55])).
% 1.62/0.59  fof(f30,plain,(
% 1.62/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.62/0.59    inference(cnf_transformation,[],[f6])).
% 1.62/0.59  fof(f6,axiom,(
% 1.62/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.62/0.59  fof(f685,plain,(
% 1.62/0.59    ( ! [X0] : (k7_subset_1(X0,sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | ~spl4_10),
% 1.62/0.59    inference(superposition,[],[f58,f668])).
% 1.62/0.59  fof(f668,plain,(
% 1.62/0.59    k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl4_10),
% 1.62/0.59    inference(duplicate_literal_removal,[],[f667])).
% 1.62/0.59  fof(f667,plain,(
% 1.62/0.59    k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl4_10),
% 1.62/0.59    inference(resolution,[],[f574,f488])).
% 1.62/0.59  fof(f488,plain,(
% 1.62/0.59    ( ! [X17,X16] : (r2_hidden(sK3(X16,X17,k1_xboole_0),X16) | k1_xboole_0 = k1_setfam_1(k2_tarski(X16,X17))) )),
% 1.62/0.59    inference(resolution,[],[f69,f105])).
% 1.62/0.59  fof(f69,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 1.62/0.59    inference(definition_unfolding,[],[f50,f35])).
% 1.62/0.59  fof(f50,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.62/0.59    inference(cnf_transformation,[],[f1])).
% 1.62/0.59  fof(f574,plain,(
% 1.62/0.59    ( ! [X28] : (~r2_hidden(sK3(X28,k2_tops_1(sK0,sK1),k1_xboole_0),sK1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X28,k2_tops_1(sK0,sK1)))) ) | ~spl4_10),
% 1.62/0.59    inference(resolution,[],[f439,f171])).
% 1.62/0.59  fof(f171,plain,(
% 1.62/0.59    ( ! [X0] : (~r2_hidden(X0,k2_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1)) ) | ~spl4_10),
% 1.62/0.59    inference(avatar_component_clause,[],[f170])).
% 1.62/0.59  fof(f439,plain,(
% 1.62/0.59    ( ! [X17,X16] : (r2_hidden(sK3(X16,X17,k1_xboole_0),X17) | k1_xboole_0 = k1_setfam_1(k2_tarski(X16,X17))) )),
% 1.62/0.59    inference(resolution,[],[f68,f105])).
% 1.62/0.59  fof(f58,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.59    inference(definition_unfolding,[],[f42,f55])).
% 1.62/0.59  fof(f42,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f24])).
% 1.62/0.59  fof(f24,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f7])).
% 1.62/0.59  fof(f7,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.62/0.59  fof(f31,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f17])).
% 1.62/0.59  fof(f17,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f12])).
% 1.62/0.59  fof(f12,axiom,(
% 1.62/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 1.62/0.59  fof(f609,plain,(
% 1.62/0.59    ~spl4_7 | ~spl4_18 | spl4_2 | ~spl4_11),
% 1.62/0.59    inference(avatar_split_clause,[],[f597,f174,f86,f370,f150])).
% 1.62/0.59  fof(f86,plain,(
% 1.62/0.59    spl4_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.62/0.59  fof(f597,plain,(
% 1.62/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_11),
% 1.62/0.59    inference(superposition,[],[f32,f176])).
% 1.62/0.59  fof(f176,plain,(
% 1.62/0.59    sK1 = k1_tops_1(sK0,sK1) | ~spl4_11),
% 1.62/0.59    inference(avatar_component_clause,[],[f174])).
% 1.62/0.59  fof(f32,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f18])).
% 1.62/0.59  fof(f18,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f10])).
% 1.62/0.59  fof(f10,axiom,(
% 1.62/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.62/0.59  fof(f403,plain,(
% 1.62/0.59    ~spl4_7 | ~spl4_1 | spl4_11 | ~spl4_3),
% 1.62/0.59    inference(avatar_split_clause,[],[f383,f92,f174,f82,f150])).
% 1.62/0.59  fof(f82,plain,(
% 1.62/0.59    spl4_1 <=> v3_pre_topc(sK1,sK0)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.62/0.59  fof(f92,plain,(
% 1.62/0.59    spl4_3 <=> ! [X1,X3] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.62/0.59  fof(f383,plain,(
% 1.62/0.59    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl4_3),
% 1.62/0.59    inference(resolution,[],[f27,f93])).
% 1.62/0.59  fof(f93,plain,(
% 1.62/0.59    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~l1_pre_topc(X1)) ) | ~spl4_3),
% 1.62/0.59    inference(avatar_component_clause,[],[f92])).
% 1.62/0.59  fof(f381,plain,(
% 1.62/0.59    spl4_18),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f380])).
% 1.62/0.59  fof(f380,plain,(
% 1.62/0.59    $false | spl4_18),
% 1.62/0.59    inference(subsumption_resolution,[],[f27,f372])).
% 1.62/0.59  fof(f372,plain,(
% 1.62/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_18),
% 1.62/0.59    inference(avatar_component_clause,[],[f370])).
% 1.62/0.59  fof(f379,plain,(
% 1.62/0.59    spl4_1 | ~spl4_11),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f378])).
% 1.62/0.59  fof(f378,plain,(
% 1.62/0.59    $false | (spl4_1 | ~spl4_11)),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f28,f29,f176,f27,f84,f80])).
% 1.62/0.59  fof(f80,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_tops_1(X1,X0) != X0 | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(X0,X1)) )),
% 1.62/0.59    inference(condensation,[],[f79])).
% 1.62/0.59  fof(f79,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) != X1 | v3_pre_topc(X1,X0)) )),
% 1.62/0.59    inference(condensation,[],[f33])).
% 1.62/0.59  fof(f33,plain,(
% 1.62/0.59    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f20])).
% 1.62/0.59  fof(f20,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.62/0.59    inference(flattening,[],[f19])).
% 1.62/0.59  fof(f19,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f11])).
% 1.62/0.59  fof(f11,axiom,(
% 1.62/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 1.62/0.59  fof(f84,plain,(
% 1.62/0.59    ~v3_pre_topc(sK1,sK0) | spl4_1),
% 1.62/0.59    inference(avatar_component_clause,[],[f82])).
% 1.62/0.59  fof(f172,plain,(
% 1.62/0.59    ~spl4_5 | spl4_10 | ~spl4_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f164,f86,f170,f138])).
% 1.62/0.59  fof(f138,plain,(
% 1.62/0.59    spl4_5 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.62/0.59  fof(f164,plain,(
% 1.62/0.59    ( ! [X0] : (~r2_hidden(X0,k2_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_2),
% 1.62/0.59    inference(superposition,[],[f124,f87])).
% 1.62/0.59  fof(f87,plain,(
% 1.62/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_2),
% 1.62/0.59    inference(avatar_component_clause,[],[f86])).
% 1.62/0.59  fof(f124,plain,(
% 1.62/0.59    ( ! [X12,X10,X13,X11] : (~r2_hidden(X13,k7_subset_1(X12,X10,X11)) | ~r2_hidden(X13,X11) | ~m1_subset_1(X10,k1_zfmisc_1(X12))) )),
% 1.62/0.59    inference(superposition,[],[f74,f58])).
% 1.62/0.59  fof(f163,plain,(
% 1.62/0.59    spl4_7),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f162])).
% 1.62/0.59  fof(f162,plain,(
% 1.62/0.59    $false | spl4_7),
% 1.62/0.59    inference(subsumption_resolution,[],[f29,f152])).
% 1.62/0.59  fof(f152,plain,(
% 1.62/0.59    ~l1_pre_topc(sK0) | spl4_7),
% 1.62/0.59    inference(avatar_component_clause,[],[f150])).
% 1.62/0.59  fof(f147,plain,(
% 1.62/0.59    spl4_5),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f145])).
% 1.62/0.59  fof(f145,plain,(
% 1.62/0.59    $false | spl4_5),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f29,f27,f140,f38])).
% 1.62/0.59  fof(f38,plain,(
% 1.62/0.59    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f23])).
% 1.62/0.59  fof(f23,plain,(
% 1.62/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.62/0.59    inference(flattening,[],[f22])).
% 1.62/0.59  fof(f22,plain,(
% 1.62/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f9])).
% 1.62/0.59  fof(f9,axiom,(
% 1.62/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.62/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.62/0.59  fof(f140,plain,(
% 1.62/0.59    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_5),
% 1.62/0.59    inference(avatar_component_clause,[],[f138])).
% 1.62/0.59  fof(f97,plain,(
% 1.62/0.59    spl4_3 | spl4_4),
% 1.62/0.59    inference(avatar_split_clause,[],[f34,f95,f92])).
% 1.62/0.59  fof(f34,plain,(
% 1.62/0.59    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 1.62/0.59    inference(cnf_transformation,[],[f20])).
% 1.62/0.59  fof(f90,plain,(
% 1.62/0.59    spl4_1 | spl4_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f25,f86,f82])).
% 1.62/0.59  fof(f25,plain,(
% 1.62/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f16])).
% 1.62/0.59  fof(f89,plain,(
% 1.62/0.59    ~spl4_1 | ~spl4_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f26,f86,f82])).
% 1.62/0.59  fof(f26,plain,(
% 1.62/0.59    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f16])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (13392)------------------------------
% 1.62/0.59  % (13392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (13392)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (13392)Memory used [KB]: 6524
% 1.62/0.59  % (13392)Time elapsed: 0.136 s
% 1.62/0.59  % (13392)------------------------------
% 1.62/0.59  % (13392)------------------------------
% 1.62/0.59  % (13378)Success in time 0.222 s
%------------------------------------------------------------------------------
