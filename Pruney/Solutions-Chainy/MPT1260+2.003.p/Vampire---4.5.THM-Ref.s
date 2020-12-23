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
% DateTime   : Thu Dec  3 13:11:32 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 576 expanded)
%              Number of leaves         :   27 ( 178 expanded)
%              Depth                    :   29
%              Number of atoms          :  340 (2124 expanded)
%              Number of equality atoms :  110 ( 719 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5638,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f139,f5537,f5544,f5551,f5637])).

fof(f5637,plain,
    ( spl5_2
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f5636])).

fof(f5636,plain,
    ( $false
    | spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f5635,f137])).

fof(f137,plain,
    ( k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_2
  <=> k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f5635,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f547,f620])).

fof(f620,plain,
    ( sK2 = k1_tops_1(sK1,sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl5_10
  <=> sK2 = k1_tops_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f547,plain,(
    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f542,f72])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ( k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
      | ~ v3_pre_topc(sK2,sK1) )
    & ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f56,f58,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK1,X1) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1)
            | ~ v3_pre_topc(X1,sK1) )
          & ( k2_tops_1(sK1,X1) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1)
            | v3_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK1,X1) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1)
          | ~ v3_pre_topc(X1,sK1) )
        & ( k2_tops_1(sK1,X1) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1)
          | v3_pre_topc(X1,sK1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
        | ~ v3_pre_topc(sK2,sK1) )
      & ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
        | v3_pre_topc(sK2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f542,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f82,f73])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f59])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f5551,plain,
    ( ~ spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f5550,f618,f614])).

fof(f614,plain,
    ( spl5_9
  <=> r1_tarski(sK2,k1_tops_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f5550,plain,
    ( sK2 = k1_tops_1(sK1,sK2)
    | ~ r1_tarski(sK2,k1_tops_1(sK1,sK2)) ),
    inference(resolution,[],[f609,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f609,plain,(
    r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
    inference(superposition,[],[f153,f604])).

fof(f604,plain,(
    k1_tops_1(sK1,sK2) = k6_subset_1(sK2,k2_tops_1(sK1,sK2)) ),
    inference(superposition,[],[f495,f312])).

fof(f312,plain,(
    ! [X13] : k7_subset_1(u1_struct_0(sK1),sK2,X13) = k6_subset_1(sK2,X13) ),
    inference(resolution,[],[f124,f73])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f108,f91])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f495,plain,(
    k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f489,f72])).

fof(f489,plain,
    ( k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f81,f73])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f153,plain,(
    ! [X2,X1] : r1_tarski(k6_subset_1(X1,X2),X1) ),
    inference(resolution,[],[f104,f87])).

fof(f87,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f5544,plain,
    ( spl5_9
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f5543,f131,f614])).

fof(f131,plain,
    ( spl5_1
  <=> v3_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f5543,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | r1_tarski(sK2,k1_tops_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1643,f127])).

fof(f127,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1643,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | r1_tarski(sK2,k1_tops_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(resolution,[],[f603,f73])).

fof(f603,plain,(
    ! [X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X17,sK1)
      | r1_tarski(X17,k1_tops_1(sK1,sK2))
      | ~ r1_tarski(X17,sK2) ) ),
    inference(subsumption_resolution,[],[f598,f72])).

fof(f598,plain,(
    ! [X17] :
      ( ~ r1_tarski(X17,sK2)
      | ~ v3_pre_topc(X17,sK1)
      | r1_tarski(X17,k1_tops_1(sK1,sK2))
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f83,f73])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
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
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f5537,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f5536])).

fof(f5536,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f5535,f154])).

fof(f154,plain,(
    r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f104,f73])).

fof(f5535,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f5534,f71])).

fof(f71,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f5534,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ r1_tarski(sK2,u1_struct_0(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f5533,f72])).

fof(f5533,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ r1_tarski(sK2,u1_struct_0(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f5515,f133])).

fof(f133,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f5515,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ r1_tarski(sK2,u1_struct_0(sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f336,f5443])).

fof(f5443,plain,
    ( sK2 = k1_tops_1(sK1,sK2)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f604,f5405])).

fof(f5405,plain,
    ( sK2 = k6_subset_1(sK2,k2_tops_1(sK1,sK2))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f5397,f4177])).

fof(f4177,plain,(
    ! [X1] : sK2 = k2_xboole_0(sK2,k6_subset_1(sK2,X1)) ),
    inference(superposition,[],[f4160,f393])).

fof(f393,plain,(
    ! [X2,X3] : k6_subset_1(X2,k6_subset_1(X3,X2)) = k2_xboole_0(X2,k6_subset_1(X2,X3)) ),
    inference(forward_demodulation,[],[f375,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f375,plain,(
    ! [X2,X3] : k6_subset_1(X2,k6_subset_1(X3,X2)) = k2_xboole_0(k6_subset_1(X2,X3),X2) ),
    inference(superposition,[],[f123,f119])).

fof(f119,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f86,f92])).

fof(f92,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f86,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f123,plain,(
    ! [X2,X0,X1] : k6_subset_1(X0,k6_subset_1(X1,X2)) = k2_xboole_0(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X2))) ),
    inference(definition_unfolding,[],[f106,f91,f91,f91,f92])).

fof(f106,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f4160,plain,(
    ! [X3] : sK2 = k6_subset_1(sK2,k6_subset_1(X3,sK2)) ),
    inference(forward_demodulation,[],[f4142,f254])).

fof(f254,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f251,f118])).

fof(f118,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f78,f91])).

fof(f78,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f251,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f121,f117])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f76,f92])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f121,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f93,f91,f92])).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f4142,plain,(
    ! [X3] : k6_subset_1(sK2,k6_subset_1(X3,sK2)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f121,f3895])).

fof(f3895,plain,(
    ! [X5] : k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,k6_subset_1(X5,sK2))) ),
    inference(forward_demodulation,[],[f3849,f120])).

fof(f120,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f88,f91])).

fof(f88,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f3849,plain,(
    ! [X5] : k1_setfam_1(k2_tarski(sK2,k6_subset_1(X5,sK2))) = k6_subset_1(sK2,k2_xboole_0(sK2,k6_subset_1(sK2,X5))) ),
    inference(superposition,[],[f1741,f393])).

fof(f1741,plain,(
    ! [X2] : k1_setfam_1(k2_tarski(sK2,X2)) = k6_subset_1(sK2,k6_subset_1(sK2,X2)) ),
    inference(superposition,[],[f387,f1374])).

fof(f1374,plain,(
    sK2 = k2_xboole_0(sK2,k3_subset_1(sK2,k1_tops_1(sK1,sK2))) ),
    inference(forward_demodulation,[],[f1373,f118])).

fof(f1373,plain,(
    k6_subset_1(sK2,k1_xboole_0) = k2_xboole_0(sK2,k3_subset_1(sK2,k1_tops_1(sK1,sK2))) ),
    inference(forward_demodulation,[],[f1365,f629])).

fof(f629,plain,(
    k3_subset_1(sK2,k1_tops_1(sK1,sK2)) = k6_subset_1(sK2,k1_tops_1(sK1,sK2)) ),
    inference(resolution,[],[f611,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f95,f91])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f611,plain,(
    m1_subset_1(k1_tops_1(sK1,sK2),k1_zfmisc_1(sK2)) ),
    inference(superposition,[],[f87,f604])).

fof(f1365,plain,(
    k6_subset_1(sK2,k1_xboole_0) = k2_xboole_0(sK2,k6_subset_1(sK2,k1_tops_1(sK1,sK2))) ),
    inference(superposition,[],[f393,f1237])).

fof(f1237,plain,(
    k1_xboole_0 = k6_subset_1(k1_tops_1(sK1,sK2),sK2) ),
    inference(superposition,[],[f1207,f604])).

fof(f1207,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(k6_subset_1(X1,X0),X1) ),
    inference(forward_demodulation,[],[f1170,f118])).

fof(f1170,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(k6_subset_1(X1,X0),k6_subset_1(X1,k1_xboole_0)) ),
    inference(superposition,[],[f382,f160])).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(superposition,[],[f120,f77])).

fof(f77,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f382,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k6_subset_1(k6_subset_1(X9,X10),k6_subset_1(X9,k6_subset_1(X10,X11))) ),
    inference(superposition,[],[f120,f123])).

fof(f387,plain,(
    ! [X4,X2,X3] : k6_subset_1(X2,k6_subset_1(k2_xboole_0(X2,X3),X4)) = k1_setfam_1(k2_tarski(X2,X4)) ),
    inference(forward_demodulation,[],[f366,f144])).

fof(f144,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f90,f77])).

fof(f366,plain,(
    ! [X4,X2,X3] : k6_subset_1(X2,k6_subset_1(k2_xboole_0(X2,X3),X4)) = k2_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(X2,X4))) ),
    inference(superposition,[],[f123,f120])).

fof(f5397,plain,
    ( k6_subset_1(sK2,k2_tops_1(sK1,sK2)) = k2_xboole_0(sK2,k6_subset_1(sK2,k2_pre_topc(sK1,sK2)))
    | ~ spl5_2 ),
    inference(superposition,[],[f393,f5212])).

fof(f5212,plain,
    ( k2_tops_1(sK1,sK2) = k6_subset_1(k2_pre_topc(sK1,sK2),sK2)
    | ~ spl5_2 ),
    inference(superposition,[],[f3390,f136])).

fof(f136,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f3390,plain,(
    ! [X28] : k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X28) = k6_subset_1(k2_pre_topc(sK1,sK2),X28) ),
    inference(subsumption_resolution,[],[f3386,f72])).

fof(f3386,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(sK1)
      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X28) = k6_subset_1(k2_pre_topc(sK1,sK2),X28) ) ),
    inference(resolution,[],[f352,f73])).

fof(f352,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_pre_topc(X5)
      | k7_subset_1(u1_struct_0(X5),k2_pre_topc(X5,X4),X6) = k6_subset_1(k2_pre_topc(X5,X4),X6) ) ),
    inference(resolution,[],[f100,f124])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f336,plain,(
    ! [X2,X1] :
      ( v3_pre_topc(k1_tops_1(X1,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ r1_tarski(X2,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f99,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f139,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f74,f135,f131])).

fof(f74,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f138,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f75,f135,f131])).

fof(f75,plain,
    ( k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (11267)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (11256)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (11272)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (11275)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (11259)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (11253)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (11264)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (11258)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (11255)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (11278)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (11257)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (11281)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (11277)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (11282)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (11269)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (11274)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (11269)Refutation not found, incomplete strategy% (11269)------------------------------
% 0.21/0.55  % (11269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11269)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11269)Memory used [KB]: 10746
% 0.21/0.55  % (11269)Time elapsed: 0.139 s
% 0.21/0.55  % (11269)------------------------------
% 0.21/0.55  % (11269)------------------------------
% 0.21/0.55  % (11270)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (11276)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (11265)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (11260)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (11266)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (11280)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (11268)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (11273)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (11262)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (11261)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (11254)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.57  % (11281)Refutation not found, incomplete strategy% (11281)------------------------------
% 0.21/0.57  % (11281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (11263)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.58  % (11281)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (11281)Memory used [KB]: 11001
% 0.21/0.58  % (11281)Time elapsed: 0.161 s
% 0.21/0.58  % (11281)------------------------------
% 0.21/0.58  % (11281)------------------------------
% 0.21/0.58  % (11271)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.59  % (11279)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.64/0.60  % (11263)Refutation not found, incomplete strategy% (11263)------------------------------
% 1.64/0.60  % (11263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.60  % (11263)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.60  
% 1.64/0.60  % (11263)Memory used [KB]: 11001
% 1.64/0.60  % (11263)Time elapsed: 0.157 s
% 1.64/0.60  % (11263)------------------------------
% 1.64/0.60  % (11263)------------------------------
% 2.18/0.65  % (11293)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.18/0.72  % (11294)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.18/0.72  % (11259)Refutation found. Thanks to Tanya!
% 2.18/0.72  % SZS status Theorem for theBenchmark
% 2.18/0.72  % SZS output start Proof for theBenchmark
% 2.18/0.72  fof(f5638,plain,(
% 2.18/0.72    $false),
% 2.18/0.72    inference(avatar_sat_refutation,[],[f138,f139,f5537,f5544,f5551,f5637])).
% 2.18/0.72  fof(f5637,plain,(
% 2.18/0.72    spl5_2 | ~spl5_10),
% 2.18/0.72    inference(avatar_contradiction_clause,[],[f5636])).
% 2.18/0.72  fof(f5636,plain,(
% 2.18/0.72    $false | (spl5_2 | ~spl5_10)),
% 2.18/0.72    inference(subsumption_resolution,[],[f5635,f137])).
% 2.18/0.72  fof(f137,plain,(
% 2.18/0.72    k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | spl5_2),
% 2.18/0.72    inference(avatar_component_clause,[],[f135])).
% 2.18/0.72  fof(f135,plain,(
% 2.18/0.72    spl5_2 <=> k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)),
% 2.18/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.18/0.72  fof(f5635,plain,(
% 2.18/0.72    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~spl5_10),
% 2.18/0.72    inference(forward_demodulation,[],[f547,f620])).
% 2.18/0.72  fof(f620,plain,(
% 2.18/0.72    sK2 = k1_tops_1(sK1,sK2) | ~spl5_10),
% 2.18/0.72    inference(avatar_component_clause,[],[f618])).
% 2.18/0.72  fof(f618,plain,(
% 2.18/0.72    spl5_10 <=> sK2 = k1_tops_1(sK1,sK2)),
% 2.18/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.18/0.72  fof(f547,plain,(
% 2.18/0.72    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2))),
% 2.18/0.72    inference(subsumption_resolution,[],[f542,f72])).
% 2.18/0.72  fof(f72,plain,(
% 2.18/0.72    l1_pre_topc(sK1)),
% 2.18/0.72    inference(cnf_transformation,[],[f59])).
% 2.18/0.72  fof(f59,plain,(
% 2.18/0.72    ((k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~v3_pre_topc(sK2,sK1)) & (k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.18/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f56,f58,f57])).
% 2.18/0.72  fof(f57,plain,(
% 2.18/0.72    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK1,X1) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | ~v3_pre_topc(X1,sK1)) & (k2_tops_1(sK1,X1) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.18/0.72    introduced(choice_axiom,[])).
% 2.18/0.72  fof(f58,plain,(
% 2.18/0.72    ? [X1] : ((k2_tops_1(sK1,X1) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | ~v3_pre_topc(X1,sK1)) & (k2_tops_1(sK1,X1) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) => ((k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~v3_pre_topc(sK2,sK1)) & (k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 2.18/0.72    introduced(choice_axiom,[])).
% 2.18/0.72  fof(f56,plain,(
% 2.18/0.72    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/0.72    inference(flattening,[],[f55])).
% 2.18/0.72  fof(f55,plain,(
% 2.18/0.72    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/0.72    inference(nnf_transformation,[],[f35])).
% 2.18/0.72  fof(f35,plain,(
% 2.18/0.72    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/0.72    inference(flattening,[],[f34])).
% 2.18/0.72  fof(f34,plain,(
% 2.18/0.72    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.18/0.72    inference(ennf_transformation,[],[f32])).
% 2.18/0.72  fof(f32,negated_conjecture,(
% 2.18/0.72    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.18/0.72    inference(negated_conjecture,[],[f31])).
% 2.18/0.72  fof(f31,conjecture,(
% 2.18/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 2.18/0.72  fof(f542,plain,(
% 2.18/0.72    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) | ~l1_pre_topc(sK1)),
% 2.18/0.72    inference(resolution,[],[f82,f73])).
% 2.18/0.72  fof(f73,plain,(
% 2.18/0.72    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.18/0.72    inference(cnf_transformation,[],[f59])).
% 2.18/0.72  fof(f82,plain,(
% 2.18/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f39])).
% 2.18/0.72  fof(f39,plain,(
% 2.18/0.72    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.72    inference(ennf_transformation,[],[f27])).
% 2.18/0.72  fof(f27,axiom,(
% 2.18/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.18/0.72  fof(f5551,plain,(
% 2.18/0.72    ~spl5_9 | spl5_10),
% 2.18/0.72    inference(avatar_split_clause,[],[f5550,f618,f614])).
% 2.18/0.72  fof(f614,plain,(
% 2.18/0.72    spl5_9 <=> r1_tarski(sK2,k1_tops_1(sK1,sK2))),
% 2.18/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.18/0.72  fof(f5550,plain,(
% 2.18/0.72    sK2 = k1_tops_1(sK1,sK2) | ~r1_tarski(sK2,k1_tops_1(sK1,sK2))),
% 2.18/0.72    inference(resolution,[],[f609,f103])).
% 2.18/0.72  fof(f103,plain,(
% 2.18/0.72    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f63])).
% 2.18/0.72  fof(f63,plain,(
% 2.18/0.72    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/0.72    inference(flattening,[],[f62])).
% 2.18/0.72  fof(f62,plain,(
% 2.18/0.72    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/0.72    inference(nnf_transformation,[],[f4])).
% 2.18/0.72  fof(f4,axiom,(
% 2.18/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.18/0.72  fof(f609,plain,(
% 2.18/0.72    r1_tarski(k1_tops_1(sK1,sK2),sK2)),
% 2.18/0.72    inference(superposition,[],[f153,f604])).
% 2.18/0.72  fof(f604,plain,(
% 2.18/0.72    k1_tops_1(sK1,sK2) = k6_subset_1(sK2,k2_tops_1(sK1,sK2))),
% 2.18/0.72    inference(superposition,[],[f495,f312])).
% 2.18/0.72  fof(f312,plain,(
% 2.18/0.72    ( ! [X13] : (k7_subset_1(u1_struct_0(sK1),sK2,X13) = k6_subset_1(sK2,X13)) )),
% 2.18/0.72    inference(resolution,[],[f124,f73])).
% 2.18/0.72  fof(f124,plain,(
% 2.18/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 2.18/0.72    inference(definition_unfolding,[],[f108,f91])).
% 2.18/0.72  fof(f91,plain,(
% 2.18/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f18])).
% 2.18/0.72  fof(f18,axiom,(
% 2.18/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.18/0.72  fof(f108,plain,(
% 2.18/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.72    inference(cnf_transformation,[],[f52])).
% 2.18/0.72  fof(f52,plain,(
% 2.18/0.72    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.72    inference(ennf_transformation,[],[f19])).
% 2.18/0.72  fof(f19,axiom,(
% 2.18/0.72    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.18/0.72  fof(f495,plain,(
% 2.18/0.72    k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2))),
% 2.18/0.72    inference(subsumption_resolution,[],[f489,f72])).
% 2.18/0.72  fof(f489,plain,(
% 2.18/0.72    k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) | ~l1_pre_topc(sK1)),
% 2.18/0.72    inference(resolution,[],[f81,f73])).
% 2.18/0.72  fof(f81,plain,(
% 2.18/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f38])).
% 2.18/0.72  fof(f38,plain,(
% 2.18/0.72    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.72    inference(ennf_transformation,[],[f30])).
% 2.18/0.72  fof(f30,axiom,(
% 2.18/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.18/0.72  fof(f153,plain,(
% 2.18/0.72    ( ! [X2,X1] : (r1_tarski(k6_subset_1(X1,X2),X1)) )),
% 2.18/0.72    inference(resolution,[],[f104,f87])).
% 2.18/0.72  fof(f87,plain,(
% 2.18/0.72    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.18/0.72    inference(cnf_transformation,[],[f14])).
% 2.18/0.72  fof(f14,axiom,(
% 2.18/0.72    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.18/0.72  fof(f104,plain,(
% 2.18/0.72    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f64])).
% 2.18/0.72  fof(f64,plain,(
% 2.18/0.72    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.18/0.72    inference(nnf_transformation,[],[f23])).
% 2.18/0.72  fof(f23,axiom,(
% 2.18/0.72    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.18/0.72  fof(f5544,plain,(
% 2.18/0.72    spl5_9 | ~spl5_1),
% 2.18/0.72    inference(avatar_split_clause,[],[f5543,f131,f614])).
% 2.18/0.72  fof(f131,plain,(
% 2.18/0.72    spl5_1 <=> v3_pre_topc(sK2,sK1)),
% 2.18/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.18/0.72  fof(f5543,plain,(
% 2.18/0.72    ~v3_pre_topc(sK2,sK1) | r1_tarski(sK2,k1_tops_1(sK1,sK2))),
% 2.18/0.72    inference(subsumption_resolution,[],[f1643,f127])).
% 2.18/0.72  fof(f127,plain,(
% 2.18/0.72    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.18/0.72    inference(equality_resolution,[],[f102])).
% 2.18/0.72  fof(f102,plain,(
% 2.18/0.72    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.18/0.72    inference(cnf_transformation,[],[f63])).
% 2.18/0.72  fof(f1643,plain,(
% 2.18/0.72    ~v3_pre_topc(sK2,sK1) | r1_tarski(sK2,k1_tops_1(sK1,sK2)) | ~r1_tarski(sK2,sK2)),
% 2.18/0.72    inference(resolution,[],[f603,f73])).
% 2.18/0.72  fof(f603,plain,(
% 2.18/0.72    ( ! [X17] : (~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X17,sK1) | r1_tarski(X17,k1_tops_1(sK1,sK2)) | ~r1_tarski(X17,sK2)) )),
% 2.18/0.72    inference(subsumption_resolution,[],[f598,f72])).
% 2.18/0.72  fof(f598,plain,(
% 2.18/0.72    ( ! [X17] : (~r1_tarski(X17,sK2) | ~v3_pre_topc(X17,sK1) | r1_tarski(X17,k1_tops_1(sK1,sK2)) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) )),
% 2.18/0.72    inference(resolution,[],[f83,f73])).
% 2.18/0.72  fof(f83,plain,(
% 2.18/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f41])).
% 2.18/0.72  fof(f41,plain,(
% 2.18/0.72    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.72    inference(flattening,[],[f40])).
% 2.18/0.72  fof(f40,plain,(
% 2.18/0.72    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.72    inference(ennf_transformation,[],[f28])).
% 2.18/0.72  fof(f28,axiom,(
% 2.18/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 2.18/0.72  fof(f5537,plain,(
% 2.18/0.72    spl5_1 | ~spl5_2),
% 2.18/0.72    inference(avatar_contradiction_clause,[],[f5536])).
% 2.18/0.72  fof(f5536,plain,(
% 2.18/0.72    $false | (spl5_1 | ~spl5_2)),
% 2.18/0.72    inference(subsumption_resolution,[],[f5535,f154])).
% 2.18/0.72  fof(f154,plain,(
% 2.18/0.72    r1_tarski(sK2,u1_struct_0(sK1))),
% 2.18/0.72    inference(resolution,[],[f104,f73])).
% 2.18/0.72  fof(f5535,plain,(
% 2.18/0.72    ~r1_tarski(sK2,u1_struct_0(sK1)) | (spl5_1 | ~spl5_2)),
% 2.18/0.72    inference(subsumption_resolution,[],[f5534,f71])).
% 2.18/0.72  fof(f71,plain,(
% 2.18/0.72    v2_pre_topc(sK1)),
% 2.18/0.72    inference(cnf_transformation,[],[f59])).
% 2.18/0.72  fof(f5534,plain,(
% 2.18/0.72    ~v2_pre_topc(sK1) | ~r1_tarski(sK2,u1_struct_0(sK1)) | (spl5_1 | ~spl5_2)),
% 2.18/0.72    inference(subsumption_resolution,[],[f5533,f72])).
% 2.18/0.72  fof(f5533,plain,(
% 2.18/0.72    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~r1_tarski(sK2,u1_struct_0(sK1)) | (spl5_1 | ~spl5_2)),
% 2.18/0.72    inference(subsumption_resolution,[],[f5515,f133])).
% 2.18/0.72  fof(f133,plain,(
% 2.18/0.72    ~v3_pre_topc(sK2,sK1) | spl5_1),
% 2.18/0.72    inference(avatar_component_clause,[],[f131])).
% 2.18/0.72  fof(f5515,plain,(
% 2.18/0.72    v3_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~r1_tarski(sK2,u1_struct_0(sK1)) | ~spl5_2),
% 2.18/0.72    inference(superposition,[],[f336,f5443])).
% 2.18/0.72  fof(f5443,plain,(
% 2.18/0.72    sK2 = k1_tops_1(sK1,sK2) | ~spl5_2),
% 2.18/0.72    inference(backward_demodulation,[],[f604,f5405])).
% 2.18/0.72  fof(f5405,plain,(
% 2.18/0.72    sK2 = k6_subset_1(sK2,k2_tops_1(sK1,sK2)) | ~spl5_2),
% 2.18/0.72    inference(forward_demodulation,[],[f5397,f4177])).
% 2.18/0.72  fof(f4177,plain,(
% 2.18/0.72    ( ! [X1] : (sK2 = k2_xboole_0(sK2,k6_subset_1(sK2,X1))) )),
% 2.18/0.72    inference(superposition,[],[f4160,f393])).
% 2.18/0.72  fof(f393,plain,(
% 2.18/0.72    ( ! [X2,X3] : (k6_subset_1(X2,k6_subset_1(X3,X2)) = k2_xboole_0(X2,k6_subset_1(X2,X3))) )),
% 2.18/0.72    inference(forward_demodulation,[],[f375,f90])).
% 2.18/0.72  fof(f90,plain,(
% 2.18/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f1])).
% 2.18/0.72  fof(f1,axiom,(
% 2.18/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.18/0.72  fof(f375,plain,(
% 2.18/0.72    ( ! [X2,X3] : (k6_subset_1(X2,k6_subset_1(X3,X2)) = k2_xboole_0(k6_subset_1(X2,X3),X2)) )),
% 2.18/0.72    inference(superposition,[],[f123,f119])).
% 2.18/0.72  fof(f119,plain,(
% 2.18/0.72    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 2.18/0.72    inference(definition_unfolding,[],[f86,f92])).
% 2.18/0.72  fof(f92,plain,(
% 2.18/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.18/0.72    inference(cnf_transformation,[],[f22])).
% 2.18/0.72  fof(f22,axiom,(
% 2.18/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.18/0.72  fof(f86,plain,(
% 2.18/0.72    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.18/0.72    inference(cnf_transformation,[],[f33])).
% 2.18/0.72  fof(f33,plain,(
% 2.18/0.72    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.18/0.72    inference(rectify,[],[f3])).
% 2.18/0.72  fof(f3,axiom,(
% 2.18/0.72    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.18/0.72  fof(f123,plain,(
% 2.18/0.72    ( ! [X2,X0,X1] : (k6_subset_1(X0,k6_subset_1(X1,X2)) = k2_xboole_0(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X2)))) )),
% 2.18/0.72    inference(definition_unfolding,[],[f106,f91,f91,f91,f92])).
% 2.18/0.72  fof(f106,plain,(
% 2.18/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.18/0.72    inference(cnf_transformation,[],[f10])).
% 2.18/0.72  fof(f10,axiom,(
% 2.18/0.72    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 2.18/0.72  fof(f4160,plain,(
% 2.18/0.72    ( ! [X3] : (sK2 = k6_subset_1(sK2,k6_subset_1(X3,sK2))) )),
% 2.18/0.72    inference(forward_demodulation,[],[f4142,f254])).
% 2.18/0.72  fof(f254,plain,(
% 2.18/0.72    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.18/0.72    inference(forward_demodulation,[],[f251,f118])).
% 2.18/0.72  fof(f118,plain,(
% 2.18/0.72    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 2.18/0.72    inference(definition_unfolding,[],[f78,f91])).
% 2.18/0.72  fof(f78,plain,(
% 2.18/0.72    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.18/0.72    inference(cnf_transformation,[],[f8])).
% 2.18/0.72  fof(f8,axiom,(
% 2.18/0.72    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.18/0.72  fof(f251,plain,(
% 2.18/0.72    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 2.18/0.72    inference(superposition,[],[f121,f117])).
% 2.18/0.72  fof(f117,plain,(
% 2.18/0.72    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 2.18/0.72    inference(definition_unfolding,[],[f76,f92])).
% 2.18/0.72  fof(f76,plain,(
% 2.18/0.72    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f7])).
% 2.18/0.72  fof(f7,axiom,(
% 2.18/0.72    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.18/0.72  fof(f121,plain,(
% 2.18/0.72    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.18/0.72    inference(definition_unfolding,[],[f93,f91,f92])).
% 2.18/0.72  fof(f93,plain,(
% 2.18/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.18/0.72    inference(cnf_transformation,[],[f5])).
% 2.18/0.72  fof(f5,axiom,(
% 2.18/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.18/0.72  fof(f4142,plain,(
% 2.18/0.72    ( ! [X3] : (k6_subset_1(sK2,k6_subset_1(X3,sK2)) = k5_xboole_0(sK2,k1_xboole_0)) )),
% 2.18/0.72    inference(superposition,[],[f121,f3895])).
% 2.18/0.72  fof(f3895,plain,(
% 2.18/0.72    ( ! [X5] : (k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,k6_subset_1(X5,sK2)))) )),
% 2.18/0.72    inference(forward_demodulation,[],[f3849,f120])).
% 2.18/0.72  fof(f120,plain,(
% 2.18/0.72    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1))) )),
% 2.18/0.72    inference(definition_unfolding,[],[f88,f91])).
% 2.18/0.72  fof(f88,plain,(
% 2.18/0.72    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.18/0.72    inference(cnf_transformation,[],[f9])).
% 2.18/0.72  fof(f9,axiom,(
% 2.18/0.72    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.18/0.72  fof(f3849,plain,(
% 2.18/0.72    ( ! [X5] : (k1_setfam_1(k2_tarski(sK2,k6_subset_1(X5,sK2))) = k6_subset_1(sK2,k2_xboole_0(sK2,k6_subset_1(sK2,X5)))) )),
% 2.18/0.72    inference(superposition,[],[f1741,f393])).
% 2.18/0.72  fof(f1741,plain,(
% 2.18/0.72    ( ! [X2] : (k1_setfam_1(k2_tarski(sK2,X2)) = k6_subset_1(sK2,k6_subset_1(sK2,X2))) )),
% 2.18/0.72    inference(superposition,[],[f387,f1374])).
% 2.18/0.72  fof(f1374,plain,(
% 2.18/0.72    sK2 = k2_xboole_0(sK2,k3_subset_1(sK2,k1_tops_1(sK1,sK2)))),
% 2.18/0.72    inference(forward_demodulation,[],[f1373,f118])).
% 2.18/0.72  fof(f1373,plain,(
% 2.18/0.72    k6_subset_1(sK2,k1_xboole_0) = k2_xboole_0(sK2,k3_subset_1(sK2,k1_tops_1(sK1,sK2)))),
% 2.18/0.72    inference(forward_demodulation,[],[f1365,f629])).
% 2.18/0.72  fof(f629,plain,(
% 2.18/0.72    k3_subset_1(sK2,k1_tops_1(sK1,sK2)) = k6_subset_1(sK2,k1_tops_1(sK1,sK2))),
% 2.18/0.72    inference(resolution,[],[f611,f122])).
% 2.18/0.72  fof(f122,plain,(
% 2.18/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.18/0.72    inference(definition_unfolding,[],[f95,f91])).
% 2.18/0.72  fof(f95,plain,(
% 2.18/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.72    inference(cnf_transformation,[],[f43])).
% 2.18/0.72  fof(f43,plain,(
% 2.18/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.72    inference(ennf_transformation,[],[f12])).
% 2.18/0.72  fof(f12,axiom,(
% 2.18/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.18/0.72  fof(f611,plain,(
% 2.18/0.72    m1_subset_1(k1_tops_1(sK1,sK2),k1_zfmisc_1(sK2))),
% 2.18/0.72    inference(superposition,[],[f87,f604])).
% 2.18/0.72  fof(f1365,plain,(
% 2.18/0.72    k6_subset_1(sK2,k1_xboole_0) = k2_xboole_0(sK2,k6_subset_1(sK2,k1_tops_1(sK1,sK2)))),
% 2.18/0.72    inference(superposition,[],[f393,f1237])).
% 2.18/0.72  fof(f1237,plain,(
% 2.18/0.72    k1_xboole_0 = k6_subset_1(k1_tops_1(sK1,sK2),sK2)),
% 2.18/0.72    inference(superposition,[],[f1207,f604])).
% 2.18/0.72  fof(f1207,plain,(
% 2.18/0.72    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(k6_subset_1(X1,X0),X1)) )),
% 2.18/0.72    inference(forward_demodulation,[],[f1170,f118])).
% 2.18/0.72  fof(f1170,plain,(
% 2.18/0.72    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(k6_subset_1(X1,X0),k6_subset_1(X1,k1_xboole_0))) )),
% 2.18/0.72    inference(superposition,[],[f382,f160])).
% 2.18/0.72  fof(f160,plain,(
% 2.18/0.72    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 2.18/0.72    inference(superposition,[],[f120,f77])).
% 2.18/0.72  fof(f77,plain,(
% 2.18/0.72    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.18/0.72    inference(cnf_transformation,[],[f6])).
% 2.18/0.72  fof(f6,axiom,(
% 2.18/0.72    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.18/0.72  fof(f382,plain,(
% 2.18/0.72    ( ! [X10,X11,X9] : (k1_xboole_0 = k6_subset_1(k6_subset_1(X9,X10),k6_subset_1(X9,k6_subset_1(X10,X11)))) )),
% 2.18/0.72    inference(superposition,[],[f120,f123])).
% 2.18/0.72  fof(f387,plain,(
% 2.18/0.72    ( ! [X4,X2,X3] : (k6_subset_1(X2,k6_subset_1(k2_xboole_0(X2,X3),X4)) = k1_setfam_1(k2_tarski(X2,X4))) )),
% 2.18/0.72    inference(forward_demodulation,[],[f366,f144])).
% 2.18/0.72  fof(f144,plain,(
% 2.18/0.72    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.18/0.72    inference(superposition,[],[f90,f77])).
% 2.18/0.72  fof(f366,plain,(
% 2.18/0.72    ( ! [X4,X2,X3] : (k6_subset_1(X2,k6_subset_1(k2_xboole_0(X2,X3),X4)) = k2_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(X2,X4)))) )),
% 2.18/0.72    inference(superposition,[],[f123,f120])).
% 2.18/0.72  fof(f5397,plain,(
% 2.18/0.72    k6_subset_1(sK2,k2_tops_1(sK1,sK2)) = k2_xboole_0(sK2,k6_subset_1(sK2,k2_pre_topc(sK1,sK2))) | ~spl5_2),
% 2.18/0.72    inference(superposition,[],[f393,f5212])).
% 2.18/0.72  fof(f5212,plain,(
% 2.18/0.72    k2_tops_1(sK1,sK2) = k6_subset_1(k2_pre_topc(sK1,sK2),sK2) | ~spl5_2),
% 2.18/0.72    inference(superposition,[],[f3390,f136])).
% 2.18/0.72  fof(f136,plain,(
% 2.18/0.72    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~spl5_2),
% 2.18/0.72    inference(avatar_component_clause,[],[f135])).
% 2.18/0.72  fof(f3390,plain,(
% 2.18/0.72    ( ! [X28] : (k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X28) = k6_subset_1(k2_pre_topc(sK1,sK2),X28)) )),
% 2.18/0.72    inference(subsumption_resolution,[],[f3386,f72])).
% 2.18/0.72  fof(f3386,plain,(
% 2.18/0.72    ( ! [X28] : (~l1_pre_topc(sK1) | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X28) = k6_subset_1(k2_pre_topc(sK1,sK2),X28)) )),
% 2.18/0.72    inference(resolution,[],[f352,f73])).
% 2.18/0.72  fof(f352,plain,(
% 2.18/0.72    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5) | k7_subset_1(u1_struct_0(X5),k2_pre_topc(X5,X4),X6) = k6_subset_1(k2_pre_topc(X5,X4),X6)) )),
% 2.18/0.72    inference(resolution,[],[f100,f124])).
% 2.18/0.72  fof(f100,plain,(
% 2.18/0.72    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/0.72    inference(cnf_transformation,[],[f50])).
% 2.18/0.72  fof(f50,plain,(
% 2.18/0.72    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.18/0.72    inference(flattening,[],[f49])).
% 2.18/0.72  fof(f49,plain,(
% 2.18/0.72    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.18/0.72    inference(ennf_transformation,[],[f24])).
% 2.18/0.72  fof(f24,axiom,(
% 2.18/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.18/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.18/0.72  fof(f336,plain,(
% 2.18/0.72    ( ! [X2,X1] : (v3_pre_topc(k1_tops_1(X1,X2),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r1_tarski(X2,u1_struct_0(X1))) )),
% 2.18/0.72    inference(resolution,[],[f99,f105])).
% 2.18/0.73  fof(f105,plain,(
% 2.18/0.73    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.18/0.73    inference(cnf_transformation,[],[f64])).
% 2.18/0.73  fof(f99,plain,(
% 2.18/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.18/0.73    inference(cnf_transformation,[],[f48])).
% 2.18/0.73  fof(f48,plain,(
% 2.18/0.73    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.18/0.73    inference(flattening,[],[f47])).
% 2.18/0.73  fof(f47,plain,(
% 2.18/0.73    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.18/0.73    inference(ennf_transformation,[],[f26])).
% 2.18/0.73  fof(f26,axiom,(
% 2.18/0.73    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.18/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.18/0.73  fof(f139,plain,(
% 2.18/0.73    spl5_1 | spl5_2),
% 2.18/0.73    inference(avatar_split_clause,[],[f74,f135,f131])).
% 2.18/0.73  fof(f74,plain,(
% 2.18/0.73    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | v3_pre_topc(sK2,sK1)),
% 2.18/0.73    inference(cnf_transformation,[],[f59])).
% 2.18/0.73  fof(f138,plain,(
% 2.18/0.73    ~spl5_1 | ~spl5_2),
% 2.18/0.73    inference(avatar_split_clause,[],[f75,f135,f131])).
% 2.18/0.73  fof(f75,plain,(
% 2.18/0.73    k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~v3_pre_topc(sK2,sK1)),
% 2.18/0.73    inference(cnf_transformation,[],[f59])).
% 2.18/0.73  % SZS output end Proof for theBenchmark
% 2.18/0.73  % (11259)------------------------------
% 2.18/0.73  % (11259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.73  % (11259)Termination reason: Refutation
% 2.18/0.73  
% 2.18/0.73  % (11259)Memory used [KB]: 14456
% 2.18/0.73  % (11259)Time elapsed: 0.257 s
% 2.18/0.73  % (11259)------------------------------
% 2.18/0.73  % (11259)------------------------------
% 2.76/0.73  % (11244)Success in time 0.365 s
%------------------------------------------------------------------------------
