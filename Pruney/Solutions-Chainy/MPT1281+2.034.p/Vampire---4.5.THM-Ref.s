%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 221 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  243 ( 644 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f496,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f116,f124,f127,f132,f204,f230,f274,f297,f461,f495])).

fof(f495,plain,(
    ~ spl2_30 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl2_30 ),
    inference(resolution,[],[f273,f48])).

fof(f48,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f28,f47])).

fof(f47,plain,(
    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f29,f27,f44])).

fof(f44,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ v5_tops_1(sK1,sK0) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f27,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f273,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl2_30
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f461,plain,
    ( ~ spl2_1
    | spl2_33 ),
    inference(avatar_contradiction_clause,[],[f460])).

fof(f460,plain,
    ( $false
    | ~ spl2_1
    | spl2_33 ),
    inference(resolution,[],[f315,f115])).

fof(f115,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_1
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f315,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_33 ),
    inference(resolution,[],[f296,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f296,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_33 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl2_33
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f297,plain,
    ( ~ spl2_9
    | ~ spl2_33
    | spl2_29 ),
    inference(avatar_split_clause,[],[f293,f268,f295,f119])).

fof(f119,plain,
    ( spl2_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f268,plain,
    ( spl2_29
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f293,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_29 ),
    inference(resolution,[],[f269,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f269,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f268])).

fof(f274,plain,
    ( ~ spl2_29
    | ~ spl2_25
    | ~ spl2_2
    | spl2_30
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f265,f202,f272,f76,f225,f268])).

fof(f225,plain,
    ( spl2_25
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f76,plain,
    ( spl2_2
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f202,plain,
    ( spl2_20
  <=> k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f265,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_20 ),
    inference(superposition,[],[f53,f203])).

fof(f203,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_subset_1(X1,X0,X2),X0)
      | ~ m1_subset_1(k9_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k9_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
      | r1_tarski(k9_subset_1(X1,X0,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f37,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f230,plain,(
    spl2_25 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl2_25 ),
    inference(resolution,[],[f226,f26])).

fof(f226,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_25 ),
    inference(avatar_component_clause,[],[f225])).

fof(f204,plain,
    ( ~ spl2_9
    | spl2_20
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f200,f73,f202,f119])).

fof(f200,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f199,f62])).

fof(f62,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f29,f27,f59])).

fof(f59,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v5_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f32,f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v5_tops_1(X1,X0)
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
          | ~ v5_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
          | ~ v5_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

fof(f199,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f192,f47])).

fof(f192,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))
    | ~ spl2_1 ),
    inference(resolution,[],[f115,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(f132,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl2_10 ),
    inference(resolution,[],[f129,f26])).

fof(f129,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_10 ),
    inference(resolution,[],[f123,f35])).

fof(f123,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl2_10
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f127,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f120,f29])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f124,plain,
    ( ~ spl2_9
    | ~ spl2_10
    | spl2_3 ),
    inference(avatar_split_clause,[],[f117,f93,f122,f119])).

fof(f93,plain,
    ( spl2_3
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f117,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_3 ),
    inference(resolution,[],[f94,f40])).

fof(f94,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f116,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f91,f73,f93])).

fof(f91,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f35,f69])).

fof(f69,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(global_subsumption,[],[f29,f66])).

fof(f66,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f30,f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f78,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f71,f76,f73])).

fof(f71,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f29,f70])).

fof(f70,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f39,f62])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (18973)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (18973)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (18981)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f496,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f78,f116,f124,f127,f132,f204,f230,f274,f297,f461,f495])).
% 0.20/0.48  fof(f495,plain,(
% 0.20/0.48    ~spl2_30),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f494])).
% 0.20/0.48  fof(f494,plain,(
% 0.20/0.48    $false | ~spl2_30),
% 0.20/0.48    inference(resolution,[],[f273,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.20/0.48    inference(backward_demodulation,[],[f28,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 0.20/0.48    inference(global_subsumption,[],[f29,f27,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | ~v5_tops_1(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f34,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f10])).
% 0.20/0.48  fof(f10,conjecture,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    v5_tops_1(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f273,plain,(
% 0.20/0.48    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_30),
% 0.20/0.48    inference(avatar_component_clause,[],[f272])).
% 0.20/0.48  fof(f272,plain,(
% 0.20/0.48    spl2_30 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.20/0.48  fof(f461,plain,(
% 0.20/0.48    ~spl2_1 | spl2_33),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f460])).
% 0.20/0.48  fof(f460,plain,(
% 0.20/0.48    $false | (~spl2_1 | spl2_33)),
% 0.20/0.48    inference(resolution,[],[f315,f115])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    spl2_1 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.48  fof(f315,plain,(
% 0.20/0.48    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_33),
% 0.20/0.48    inference(resolution,[],[f296,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.48  fof(f296,plain,(
% 0.20/0.48    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_33),
% 0.20/0.48    inference(avatar_component_clause,[],[f295])).
% 0.20/0.48  fof(f295,plain,(
% 0.20/0.48    spl2_33 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.20/0.48  fof(f297,plain,(
% 0.20/0.48    ~spl2_9 | ~spl2_33 | spl2_29),
% 0.20/0.48    inference(avatar_split_clause,[],[f293,f268,f295,f119])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    spl2_9 <=> l1_pre_topc(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.48  fof(f268,plain,(
% 0.20/0.48    spl2_29 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.20/0.48  fof(f293,plain,(
% 0.20/0.48    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_29),
% 0.20/0.48    inference(resolution,[],[f269,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.48  fof(f269,plain,(
% 0.20/0.48    ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_29),
% 0.20/0.48    inference(avatar_component_clause,[],[f268])).
% 0.20/0.48  fof(f274,plain,(
% 0.20/0.48    ~spl2_29 | ~spl2_25 | ~spl2_2 | spl2_30 | ~spl2_20),
% 0.20/0.48    inference(avatar_split_clause,[],[f265,f202,f272,f76,f225,f268])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    spl2_25 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl2_2 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    spl2_20 <=> k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.48  fof(f265,plain,(
% 0.20/0.48    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_20),
% 0.20/0.48    inference(superposition,[],[f53,f203])).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) | ~spl2_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f202])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X1,X0,X2),X0) | ~m1_subset_1(k9_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k9_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) | r1_tarski(k9_subset_1(X1,X0,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(resolution,[],[f37,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.20/0.48  fof(f230,plain,(
% 0.20/0.48    spl2_25),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f229])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    $false | spl2_25),
% 0.20/0.48    inference(resolution,[],[f226,f26])).
% 0.20/0.48  fof(f226,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_25),
% 0.20/0.48    inference(avatar_component_clause,[],[f225])).
% 0.20/0.48  fof(f204,plain,(
% 0.20/0.48    ~spl2_9 | spl2_20 | ~spl2_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f200,f73,f202,f119])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.20/0.48    inference(forward_demodulation,[],[f199,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 0.20/0.48    inference(global_subsumption,[],[f29,f27,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | ~v5_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 0.20/0.48    inference(resolution,[],[f32,f26])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v5_tops_1(X1,X0) | k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) | ~v5_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.20/0.48    inference(forward_demodulation,[],[f192,f47])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) | ~spl2_1),
% 0.20/0.48    inference(resolution,[],[f115,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    spl2_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f131])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    $false | spl2_10),
% 0.20/0.48    inference(resolution,[],[f129,f26])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_10),
% 0.20/0.48    inference(resolution,[],[f123,f35])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f122])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    spl2_10 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    spl2_9),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f126])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    $false | spl2_9),
% 0.20/0.48    inference(resolution,[],[f120,f29])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | spl2_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f119])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ~spl2_9 | ~spl2_10 | spl2_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f117,f93,f122,f119])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    spl2_3 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_3),
% 0.20/0.48    inference(resolution,[],[f94,f40])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f93])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ~spl2_3 | spl2_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f91,f73,f93])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(superposition,[],[f35,f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.48    inference(global_subsumption,[],[f29,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.48    inference(resolution,[],[f30,f26])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ~spl2_1 | spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f71,f76,f73])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(global_subsumption,[],[f29,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.48    inference(superposition,[],[f39,f62])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (18973)------------------------------
% 0.20/0.48  % (18973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18973)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (18973)Memory used [KB]: 10874
% 0.20/0.48  % (18973)Time elapsed: 0.065 s
% 0.20/0.48  % (18973)------------------------------
% 0.20/0.48  % (18973)------------------------------
% 0.20/0.48  % (18960)Success in time 0.132 s
%------------------------------------------------------------------------------
