%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 194 expanded)
%              Number of leaves         :   15 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  274 ( 701 expanded)
%              Number of equality atoms :   55 ( 163 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f145,f151,f209])).

fof(f209,plain,
    ( ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f207,f170])).

fof(f170,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f169,f35])).

fof(f35,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).

fof(f169,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(resolution,[],[f163,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f163,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f162,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f162,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f154,f144])).

fof(f144,plain,
    ( v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl2_11
  <=> v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f154,plain,
    ( ~ v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_10 ),
    inference(resolution,[],[f139,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f139,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl2_10
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f207,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl2_10 ),
    inference(trivial_inequality_removal,[],[f206])).

fof(f206,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl2_10 ),
    inference(superposition,[],[f46,f204])).

fof(f204,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl2_10 ),
    inference(superposition,[],[f165,f157])).

fof(f157,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)
    | ~ spl2_10 ),
    inference(resolution,[],[f139,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f165,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f164,f60])).

fof(f60,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f59,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f52,f33])).

fof(f52,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f164,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f156,f33])).

fof(f156,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_10 ),
    inference(resolution,[],[f139,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f151,plain,
    ( ~ spl2_4
    | spl2_10 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl2_4
    | spl2_10 ),
    inference(subsumption_resolution,[],[f149,f33])).

fof(f149,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | spl2_10 ),
    inference(subsumption_resolution,[],[f148,f84])).

fof(f84,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_4
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f148,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_10 ),
    inference(resolution,[],[f140,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f140,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f145,plain,
    ( ~ spl2_10
    | spl2_11
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f136,f83,f142,f138])).

fof(f136,plain,
    ( v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f135,f33])).

fof(f135,plain,
    ( v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f134,f32])).

fof(f134,plain,
    ( v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1))
    | v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(superposition,[],[f38,f102])).

fof(f102,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f101,f32])).

fof(f101,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f95,f33])).

fof(f95,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f84,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l79_tops_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f94,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f92,f33])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_4 ),
    inference(subsumption_resolution,[],[f91,f34])).

fof(f91,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_4 ),
    inference(resolution,[],[f85,f42])).

fof(f85,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (3788)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.47  % (3777)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.47  % (3777)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (3797)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f94,f145,f151,f209])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ~spl2_10 | ~spl2_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    $false | (~spl2_10 | ~spl2_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f207,f170])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | (~spl2_10 | ~spl2_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f27,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | (~spl2_10 | ~spl2_11)),
% 0.21/0.48    inference(resolution,[],[f163,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_10 | ~spl2_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f162,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0) | (~spl2_10 | ~spl2_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f154,f144])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | ~spl2_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f142])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl2_11 <=> v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~spl2_10),
% 0.21/0.48    inference(resolution,[],[f139,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f138])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl2_10 <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | ~spl2_10),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f206])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | ~spl2_10),
% 0.21/0.48    inference(superposition,[],[f46,f204])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | ~spl2_10),
% 0.21/0.48    inference(superposition,[],[f165,f157])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)) ) | ~spl2_10),
% 0.21/0.48    inference(resolution,[],[f139,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | ~spl2_10),
% 0.21/0.48    inference(forward_demodulation,[],[f164,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f59,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f52,f33])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f34,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | ~spl2_10),
% 0.21/0.48    inference(subsumption_resolution,[],[f156,f33])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | ~l1_pre_topc(sK0) | ~spl2_10),
% 0.21/0.48    inference(resolution,[],[f139,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~spl2_4 | spl2_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    $false | (~spl2_4 | spl2_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f33])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (~spl2_4 | spl2_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl2_4 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_10),
% 0.21/0.48    inference(resolution,[],[f140,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f138])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ~spl2_10 | spl2_11 | ~spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f136,f83,f142,f138])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f33])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f32])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1)) | v4_pre_topc(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.48    inference(superposition,[],[f38,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~spl2_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f101,f32])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~v2_pre_topc(sK0) | ~spl2_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f95,f33])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_4),
% 0.21/0.48    inference(resolution,[],[f84,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l79_tops_1)).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl2_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    $false | spl2_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f33])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | spl2_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f34])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_4),
% 0.21/0.48    inference(resolution,[],[f85,f42])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (3777)------------------------------
% 0.21/0.48  % (3777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3777)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (3777)Memory used [KB]: 10618
% 0.21/0.48  % (3777)Time elapsed: 0.063 s
% 0.21/0.48  % (3777)------------------------------
% 0.21/0.48  % (3777)------------------------------
% 0.21/0.48  % (3775)Success in time 0.124 s
%------------------------------------------------------------------------------
