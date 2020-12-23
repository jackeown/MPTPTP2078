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
% DateTime   : Thu Dec  3 13:12:17 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 674 expanded)
%              Number of leaves         :   24 ( 232 expanded)
%              Depth                    :   17
%              Number of atoms          :  434 (3237 expanded)
%              Number of equality atoms :   92 ( 616 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f106,f153,f155,f172,f174,f366,f398,f418])).

fof(f418,plain,
    ( spl5_10
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl5_10
    | ~ spl5_12 ),
    inference(resolution,[],[f407,f355])).

fof(f355,plain,
    ( ~ sP0(k2_struct_0(sK1),sK3,sK3)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl5_10
  <=> sP0(k2_struct_0(sK1),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f407,plain,
    ( sP0(k2_struct_0(sK1),sK3,sK3)
    | ~ spl5_12 ),
    inference(superposition,[],[f64,f364])).

fof(f364,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl5_12
  <=> sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f64,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f59,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f398,plain,
    ( ~ spl5_1
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(trivial_inequality_removal,[],[f396])).

fof(f396,plain,
    ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,sK3)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(superposition,[],[f87,f371])).

fof(f371,plain,
    ( k2_pre_topc(sK1,sK3) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f177,f370])).

fof(f370,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1)))
    | ~ spl5_10 ),
    inference(resolution,[],[f356,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f60,f49])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f356,plain,
    ( sP0(k2_struct_0(sK1),sK3,sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f354])).

fof(f177,plain,
    ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1))))
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f175,f99])).

fof(f99,plain,
    ( k2_struct_0(sK1) = k2_pre_topc(sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_1
  <=> k2_struct_0(sK1) = k2_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f175,plain,
    ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_pre_topc(sK1,sK2))))
    | ~ spl5_6 ),
    inference(resolution,[],[f171,f69])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f38,f68])).

fof(f68,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f65,f37])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2))
    & v3_pre_topc(sK3,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & v1_tops_1(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,X1))
              & v3_pre_topc(X2,sK1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & v1_tops_1(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,X1))
            & v3_pre_topc(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
        & v1_tops_1(X1,sK1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,sK2))
          & v3_pre_topc(X2,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & v1_tops_1(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,sK2))
        & v3_pre_topc(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2))
      & v3_pre_topc(sK3,sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | k2_pre_topc(sK1,k1_setfam_1(k2_tarski(X0,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_pre_topc(sK1,X0)))) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl5_6
  <=> ! [X0] :
        ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(X0,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_pre_topc(sK1,X0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f87,plain,(
    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(forward_demodulation,[],[f86,f75])).

fof(f75,plain,(
    ! [X2,X3] : k1_setfam_1(k2_tarski(X2,X3)) = k1_setfam_1(k2_tarski(X3,X2)) ),
    inference(resolution,[],[f62,f66])).

fof(f66,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_setfam_1(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f64,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f86,plain,(
    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2))) ),
    inference(backward_demodulation,[],[f82,f85])).

fof(f85,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK1),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(backward_demodulation,[],[f80,f83])).

fof(f83,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK1),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(resolution,[],[f61,f69])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f51,f49])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f80,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK1),X0,sK2) = k9_subset_1(k2_struct_0(sK1),sK2,X0) ),
    inference(resolution,[],[f52,f69])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f82,plain,(
    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK2,sK3)) ),
    inference(backward_demodulation,[],[f71,f80])).

fof(f71,plain,(
    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2)) ),
    inference(backward_demodulation,[],[f42,f68])).

fof(f42,plain,(
    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f366,plain,
    ( spl5_10
    | spl5_12 ),
    inference(avatar_split_clause,[],[f348,f362,f354])).

fof(f348,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1)))
    | sP0(k2_struct_0(sK1),sK3,sK3) ),
    inference(resolution,[],[f226,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f226,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(k2_struct_0(sK1),X1,X1),sK3)
      | k1_setfam_1(k2_tarski(X1,k2_struct_0(sK1))) = X1 ) ),
    inference(resolution,[],[f141,f70])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f40,f68])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f141,plain,(
    ! [X17,X18,X16] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | ~ r2_hidden(sK4(X17,X16,X16),X18)
      | k1_setfam_1(k2_tarski(X16,X17)) = X16 ) ),
    inference(resolution,[],[f133,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X1),X0)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X1),X0)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1
      | k1_setfam_1(k2_tarski(X1,X0)) = X1 ) ),
    inference(resolution,[],[f126,f62])).

fof(f126,plain,(
    ! [X4,X5] :
      ( sP0(X5,X4,X4)
      | ~ r2_hidden(sK4(X5,X4,X4),X5)
      | k1_setfam_1(k2_tarski(X4,X5)) = X4 ) ),
    inference(resolution,[],[f123,f111])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X1),X1)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1
      | ~ r2_hidden(sK4(X0,X1,X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X1),X0)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1
      | ~ r2_hidden(sK4(X0,X1,X1),X1)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1 ) ),
    inference(resolution,[],[f116,f62])).

fof(f116,plain,(
    ! [X6,X7] :
      ( sP0(X6,X7,X7)
      | ~ r2_hidden(sK4(X6,X7,X7),X6)
      | k1_setfam_1(k2_tarski(X7,X6)) = X7
      | ~ r2_hidden(sK4(X6,X7,X7),X7) ) ),
    inference(resolution,[],[f113,f111])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X1,X0)) = X2 ) ),
    inference(resolution,[],[f58,f62])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f174,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f168,f70])).

fof(f168,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f172,plain,
    ( ~ spl5_5
    | spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f164,f151,f170,f166])).

fof(f151,plain,
    ( spl5_4
  <=> ! [X1,X0] :
        ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,X1))
        | ~ v3_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f164,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(X0,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_pre_topc(sK1,X0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f163,f75])).

fof(f163,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK1,k1_setfam_1(k2_tarski(X0,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(k2_pre_topc(sK1,X0),sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f162,f88])).

fof(f88,plain,(
    ! [X1] : k9_subset_1(k2_struct_0(sK1),sK3,X1) = k1_setfam_1(k2_tarski(X1,sK3)) ),
    inference(backward_demodulation,[],[f81,f84])).

fof(f84,plain,(
    ! [X1] : k9_subset_1(k2_struct_0(sK1),X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3)) ),
    inference(resolution,[],[f61,f70])).

fof(f81,plain,(
    ! [X1] : k9_subset_1(k2_struct_0(sK1),X1,sK3) = k9_subset_1(k2_struct_0(sK1),sK3,X1) ),
    inference(resolution,[],[f52,f70])).

fof(f162,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(X0,sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f161,f88])).

fof(f161,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f152,f41])).

fof(f41,plain,(
    v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK1)
        | k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f151])).

fof(f155,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl5_3 ),
    inference(resolution,[],[f149,f37])).

fof(f149,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl5_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f153,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f145,f151,f147])).

fof(f145,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(forward_demodulation,[],[f144,f68])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1)
      | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,X1)) ) ),
    inference(forward_demodulation,[],[f143,f68])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,X1)) ) ),
    inference(forward_demodulation,[],[f142,f68])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,X1)) ) ),
    inference(resolution,[],[f47,f36])).

fof(f36,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

fof(f106,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f103,f69])).

fof(f103,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f104,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f95,f101,f97])).

fof(f95,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1)))
    | k2_struct_0(sK1) = k2_pre_topc(sK1,sK2) ),
    inference(resolution,[],[f94,f39])).

fof(f39,plain,(
    v1_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | k2_struct_0(sK1) = k2_pre_topc(sK1,X0) ) ),
    inference(forward_demodulation,[],[f93,f68])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_struct_0(sK1) = k2_pre_topc(sK1,X0) ) ),
    inference(resolution,[],[f45,f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:04:49 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.21/0.52  % (10884)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (10903)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (10891)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (10895)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (10901)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (10886)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (10881)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (10889)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (10891)Refutation not found, incomplete strategy% (10891)------------------------------
% 0.21/0.54  % (10891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10887)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (10882)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (10885)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (10890)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (10889)Refutation not found, incomplete strategy% (10889)------------------------------
% 0.21/0.55  % (10889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10880)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (10905)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (10890)Refutation not found, incomplete strategy% (10890)------------------------------
% 0.21/0.55  % (10890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10890)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10890)Memory used [KB]: 10746
% 0.21/0.55  % (10890)Time elapsed: 0.134 s
% 0.21/0.55  % (10890)------------------------------
% 0.21/0.55  % (10890)------------------------------
% 0.21/0.55  % (10908)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (10880)Refutation not found, incomplete strategy% (10880)------------------------------
% 0.21/0.55  % (10880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10880)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10880)Memory used [KB]: 1791
% 0.21/0.55  % (10880)Time elapsed: 0.138 s
% 0.21/0.55  % (10880)------------------------------
% 0.21/0.55  % (10880)------------------------------
% 0.21/0.55  % (10897)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (10902)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (10891)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10891)Memory used [KB]: 10746
% 0.21/0.55  % (10891)Time elapsed: 0.132 s
% 0.21/0.55  % (10891)------------------------------
% 0.21/0.55  % (10891)------------------------------
% 0.21/0.55  % (10883)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (10897)Refutation not found, incomplete strategy% (10897)------------------------------
% 0.21/0.55  % (10897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10897)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10897)Memory used [KB]: 10618
% 0.21/0.55  % (10897)Time elapsed: 0.140 s
% 0.21/0.55  % (10897)------------------------------
% 0.21/0.55  % (10897)------------------------------
% 0.21/0.55  % (10899)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (10893)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (10906)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (10904)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (10889)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10889)Memory used [KB]: 10746
% 0.21/0.56  % (10889)Time elapsed: 0.129 s
% 0.21/0.56  % (10889)------------------------------
% 0.21/0.56  % (10889)------------------------------
% 0.21/0.56  % (10894)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (10892)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (10888)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (10902)Refutation not found, incomplete strategy% (10902)------------------------------
% 0.21/0.56  % (10902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10888)Refutation not found, incomplete strategy% (10888)------------------------------
% 0.21/0.56  % (10888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10888)Memory used [KB]: 10746
% 0.21/0.56  % (10888)Time elapsed: 0.151 s
% 0.21/0.56  % (10888)------------------------------
% 0.21/0.56  % (10888)------------------------------
% 0.21/0.56  % (10907)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (10882)Refutation not found, incomplete strategy% (10882)------------------------------
% 0.21/0.57  % (10882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10898)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (10896)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (10909)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (10882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (10882)Memory used [KB]: 10874
% 0.21/0.57  % (10882)Time elapsed: 0.141 s
% 0.21/0.57  % (10882)------------------------------
% 0.21/0.57  % (10882)------------------------------
% 0.21/0.57  % (10900)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (10902)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (10902)Memory used [KB]: 10746
% 0.21/0.58  % (10902)Time elapsed: 0.136 s
% 0.21/0.58  % (10902)------------------------------
% 0.21/0.58  % (10902)------------------------------
% 0.21/0.58  % (10900)Refutation not found, incomplete strategy% (10900)------------------------------
% 0.21/0.58  % (10900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (10900)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (10900)Memory used [KB]: 10874
% 0.21/0.58  % (10900)Time elapsed: 0.156 s
% 0.21/0.58  % (10900)------------------------------
% 0.21/0.58  % (10900)------------------------------
% 1.70/0.59  % (10892)Refutation found. Thanks to Tanya!
% 1.70/0.59  % SZS status Theorem for theBenchmark
% 1.85/0.61  % SZS output start Proof for theBenchmark
% 1.85/0.61  fof(f419,plain,(
% 1.85/0.61    $false),
% 1.85/0.61    inference(avatar_sat_refutation,[],[f104,f106,f153,f155,f172,f174,f366,f398,f418])).
% 1.85/0.61  fof(f418,plain,(
% 1.85/0.61    spl5_10 | ~spl5_12),
% 1.85/0.61    inference(avatar_contradiction_clause,[],[f413])).
% 1.85/0.61  fof(f413,plain,(
% 1.85/0.61    $false | (spl5_10 | ~spl5_12)),
% 1.85/0.61    inference(resolution,[],[f407,f355])).
% 1.85/0.61  fof(f355,plain,(
% 1.85/0.61    ~sP0(k2_struct_0(sK1),sK3,sK3) | spl5_10),
% 1.85/0.61    inference(avatar_component_clause,[],[f354])).
% 1.85/0.61  fof(f354,plain,(
% 1.85/0.61    spl5_10 <=> sP0(k2_struct_0(sK1),sK3,sK3)),
% 1.85/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.85/0.61  fof(f407,plain,(
% 1.85/0.61    sP0(k2_struct_0(sK1),sK3,sK3) | ~spl5_12),
% 1.85/0.61    inference(superposition,[],[f64,f364])).
% 1.85/0.61  fof(f364,plain,(
% 1.85/0.61    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1))) | ~spl5_12),
% 1.85/0.61    inference(avatar_component_clause,[],[f362])).
% 1.85/0.61  fof(f362,plain,(
% 1.85/0.61    spl5_12 <=> sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1)))),
% 1.85/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.85/0.61  fof(f64,plain,(
% 1.85/0.61    ( ! [X0,X1] : (sP0(X1,X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.85/0.61    inference(equality_resolution,[],[f63])).
% 1.85/0.61  fof(f63,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.85/0.61    inference(definition_unfolding,[],[f59,f49])).
% 1.85/0.61  fof(f49,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.85/0.61    inference(cnf_transformation,[],[f6])).
% 1.85/0.61  fof(f6,axiom,(
% 1.85/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.85/0.61  fof(f59,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.85/0.61    inference(cnf_transformation,[],[f35])).
% 1.85/0.61  fof(f35,plain,(
% 1.85/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.85/0.61    inference(nnf_transformation,[],[f24])).
% 1.85/0.61  fof(f24,plain,(
% 1.85/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.85/0.61    inference(definition_folding,[],[f1,f23])).
% 1.85/0.61  fof(f23,plain,(
% 1.85/0.61    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.85/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.85/0.61  fof(f1,axiom,(
% 1.85/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.85/0.61  fof(f398,plain,(
% 1.85/0.61    ~spl5_1 | ~spl5_6 | ~spl5_10),
% 1.85/0.61    inference(avatar_contradiction_clause,[],[f397])).
% 1.85/0.61  fof(f397,plain,(
% 1.85/0.61    $false | (~spl5_1 | ~spl5_6 | ~spl5_10)),
% 1.85/0.61    inference(trivial_inequality_removal,[],[f396])).
% 1.85/0.61  fof(f396,plain,(
% 1.85/0.61    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,sK3) | (~spl5_1 | ~spl5_6 | ~spl5_10)),
% 1.85/0.61    inference(superposition,[],[f87,f371])).
% 1.85/0.61  fof(f371,plain,(
% 1.85/0.61    k2_pre_topc(sK1,sK3) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) | (~spl5_1 | ~spl5_6 | ~spl5_10)),
% 1.85/0.61    inference(backward_demodulation,[],[f177,f370])).
% 1.85/0.61  fof(f370,plain,(
% 1.85/0.61    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1))) | ~spl5_10),
% 1.85/0.61    inference(resolution,[],[f356,f62])).
% 1.85/0.61  fof(f62,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 1.85/0.61    inference(definition_unfolding,[],[f60,f49])).
% 1.85/0.61  fof(f60,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f35])).
% 1.85/0.61  fof(f356,plain,(
% 1.85/0.61    sP0(k2_struct_0(sK1),sK3,sK3) | ~spl5_10),
% 1.85/0.61    inference(avatar_component_clause,[],[f354])).
% 1.85/0.61  fof(f177,plain,(
% 1.85/0.61    k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1)))) | (~spl5_1 | ~spl5_6)),
% 1.85/0.61    inference(forward_demodulation,[],[f175,f99])).
% 1.85/0.61  fof(f99,plain,(
% 1.85/0.61    k2_struct_0(sK1) = k2_pre_topc(sK1,sK2) | ~spl5_1),
% 1.85/0.61    inference(avatar_component_clause,[],[f97])).
% 1.85/0.61  fof(f97,plain,(
% 1.85/0.61    spl5_1 <=> k2_struct_0(sK1) = k2_pre_topc(sK1,sK2)),
% 1.85/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.85/0.61  fof(f175,plain,(
% 1.85/0.61    k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_pre_topc(sK1,sK2)))) | ~spl5_6),
% 1.85/0.61    inference(resolution,[],[f171,f69])).
% 1.85/0.61  fof(f69,plain,(
% 1.85/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.85/0.61    inference(backward_demodulation,[],[f38,f68])).
% 1.85/0.61  fof(f68,plain,(
% 1.85/0.61    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.85/0.61    inference(resolution,[],[f65,f37])).
% 1.85/0.61  fof(f37,plain,(
% 1.85/0.61    l1_pre_topc(sK1)),
% 1.85/0.61    inference(cnf_transformation,[],[f28])).
% 1.85/0.61  fof(f28,plain,(
% 1.85/0.61    ((k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) & v3_pre_topc(sK3,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_1(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 1.85/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f27,f26,f25])).
% 1.85/0.61  fof(f25,plain,(
% 1.85/0.61    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,X1)) & v3_pre_topc(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_1(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.85/0.61    introduced(choice_axiom,[])).
% 1.85/0.61  fof(f26,plain,(
% 1.85/0.61    ? [X1] : (? [X2] : (k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,X1)) & v3_pre_topc(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_1(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X2] : (k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,sK2)) & v3_pre_topc(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & v1_tops_1(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.85/0.61    introduced(choice_axiom,[])).
% 1.85/0.61  fof(f27,plain,(
% 1.85/0.61    ? [X2] : (k2_pre_topc(sK1,X2) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X2,sK2)) & v3_pre_topc(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) => (k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2)) & v3_pre_topc(sK3,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.85/0.61    introduced(choice_axiom,[])).
% 1.85/0.61  fof(f14,plain,(
% 1.85/0.61    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.85/0.61    inference(flattening,[],[f13])).
% 1.85/0.61  fof(f13,plain,(
% 1.85/0.61    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.85/0.61    inference(ennf_transformation,[],[f12])).
% 1.85/0.61  fof(f12,negated_conjecture,(
% 1.85/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.85/0.61    inference(negated_conjecture,[],[f11])).
% 1.85/0.61  fof(f11,conjecture,(
% 1.85/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 1.85/0.61  fof(f65,plain,(
% 1.85/0.61    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.85/0.61    inference(resolution,[],[f43,f44])).
% 1.85/0.61  fof(f44,plain,(
% 1.85/0.61    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f16])).
% 1.85/0.61  fof(f16,plain,(
% 1.85/0.61    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.85/0.61    inference(ennf_transformation,[],[f8])).
% 1.85/0.61  fof(f8,axiom,(
% 1.85/0.61    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.85/0.61  fof(f43,plain,(
% 1.85/0.61    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f15])).
% 1.85/0.61  fof(f15,plain,(
% 1.85/0.61    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.85/0.61    inference(ennf_transformation,[],[f7])).
% 1.85/0.61  fof(f7,axiom,(
% 1.85/0.61    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.85/0.61  fof(f38,plain,(
% 1.85/0.61    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.85/0.61    inference(cnf_transformation,[],[f28])).
% 1.85/0.61  fof(f171,plain,(
% 1.85/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | k2_pre_topc(sK1,k1_setfam_1(k2_tarski(X0,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_pre_topc(sK1,X0))))) ) | ~spl5_6),
% 1.85/0.61    inference(avatar_component_clause,[],[f170])).
% 1.85/0.61  fof(f170,plain,(
% 1.85/0.61    spl5_6 <=> ! [X0] : (k2_pre_topc(sK1,k1_setfam_1(k2_tarski(X0,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_pre_topc(sK1,X0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))))),
% 1.85/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.85/0.61  fof(f87,plain,(
% 1.85/0.61    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))),
% 1.85/0.61    inference(forward_demodulation,[],[f86,f75])).
% 1.85/0.61  fof(f75,plain,(
% 1.85/0.61    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(X2,X3)) = k1_setfam_1(k2_tarski(X3,X2))) )),
% 1.85/0.61    inference(resolution,[],[f62,f66])).
% 1.85/0.61  fof(f66,plain,(
% 1.85/0.61    ( ! [X0,X1] : (sP0(X1,X0,k1_setfam_1(k2_tarski(X1,X0)))) )),
% 1.85/0.61    inference(superposition,[],[f64,f48])).
% 1.85/0.61  fof(f48,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f2])).
% 1.85/0.61  fof(f2,axiom,(
% 1.85/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.85/0.61  fof(f86,plain,(
% 1.85/0.61    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,sK2)))),
% 1.85/0.61    inference(backward_demodulation,[],[f82,f85])).
% 1.85/0.61  fof(f85,plain,(
% 1.85/0.61    ( ! [X0] : (k9_subset_1(k2_struct_0(sK1),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2))) )),
% 1.85/0.61    inference(backward_demodulation,[],[f80,f83])).
% 1.85/0.61  fof(f83,plain,(
% 1.85/0.61    ( ! [X0] : (k9_subset_1(k2_struct_0(sK1),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) )),
% 1.85/0.61    inference(resolution,[],[f61,f69])).
% 1.85/0.61  fof(f61,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.85/0.61    inference(definition_unfolding,[],[f51,f49])).
% 1.85/0.61  fof(f51,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.85/0.61    inference(cnf_transformation,[],[f21])).
% 1.85/0.61  fof(f21,plain,(
% 1.85/0.61    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.85/0.61    inference(ennf_transformation,[],[f5])).
% 1.85/0.61  fof(f5,axiom,(
% 1.85/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.85/0.61  fof(f80,plain,(
% 1.85/0.61    ( ! [X0] : (k9_subset_1(k2_struct_0(sK1),X0,sK2) = k9_subset_1(k2_struct_0(sK1),sK2,X0)) )),
% 1.85/0.61    inference(resolution,[],[f52,f69])).
% 1.85/0.61  fof(f52,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f22])).
% 1.85/0.61  fof(f22,plain,(
% 1.85/0.61    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.85/0.61    inference(ennf_transformation,[],[f3])).
% 1.85/0.61  fof(f3,axiom,(
% 1.85/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.85/0.61  fof(f82,plain,(
% 1.85/0.61    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK2,sK3))),
% 1.85/0.61    inference(backward_demodulation,[],[f71,f80])).
% 1.85/0.61  fof(f71,plain,(
% 1.85/0.61    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,sK2))),
% 1.85/0.61    inference(backward_demodulation,[],[f42,f68])).
% 1.85/0.61  fof(f42,plain,(
% 1.85/0.61    k2_pre_topc(sK1,sK3) != k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),sK3,sK2))),
% 1.85/0.61    inference(cnf_transformation,[],[f28])).
% 1.85/0.61  fof(f366,plain,(
% 1.85/0.61    spl5_10 | spl5_12),
% 1.85/0.61    inference(avatar_split_clause,[],[f348,f362,f354])).
% 1.85/0.61  fof(f348,plain,(
% 1.85/0.61    sK3 = k1_setfam_1(k2_tarski(sK3,k2_struct_0(sK1))) | sP0(k2_struct_0(sK1),sK3,sK3)),
% 1.85/0.61    inference(resolution,[],[f226,f111])).
% 1.85/0.61  fof(f111,plain,(
% 1.85/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 1.85/0.61    inference(factoring,[],[f56])).
% 1.85/0.61  fof(f56,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f34])).
% 1.85/0.61  fof(f34,plain,(
% 1.85/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.85/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 1.85/0.61  fof(f33,plain,(
% 1.85/0.61    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.85/0.61    introduced(choice_axiom,[])).
% 1.85/0.61  fof(f32,plain,(
% 1.85/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.85/0.61    inference(rectify,[],[f31])).
% 1.85/0.61  fof(f31,plain,(
% 1.85/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.85/0.61    inference(flattening,[],[f30])).
% 1.85/0.61  fof(f30,plain,(
% 1.85/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.85/0.61    inference(nnf_transformation,[],[f23])).
% 1.85/0.61  fof(f226,plain,(
% 1.85/0.61    ( ! [X1] : (~r2_hidden(sK4(k2_struct_0(sK1),X1,X1),sK3) | k1_setfam_1(k2_tarski(X1,k2_struct_0(sK1))) = X1) )),
% 1.85/0.61    inference(resolution,[],[f141,f70])).
% 1.85/0.61  fof(f70,plain,(
% 1.85/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.85/0.61    inference(backward_demodulation,[],[f40,f68])).
% 1.85/0.61  fof(f40,plain,(
% 1.85/0.61    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.85/0.61    inference(cnf_transformation,[],[f28])).
% 1.85/0.61  fof(f141,plain,(
% 1.85/0.61    ( ! [X17,X18,X16] : (~m1_subset_1(X18,k1_zfmisc_1(X17)) | ~r2_hidden(sK4(X17,X16,X16),X18) | k1_setfam_1(k2_tarski(X16,X17)) = X16) )),
% 1.85/0.61    inference(resolution,[],[f133,f50])).
% 1.85/0.61  fof(f50,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.85/0.61    inference(cnf_transformation,[],[f20])).
% 1.85/0.61  fof(f20,plain,(
% 1.85/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.85/0.61    inference(ennf_transformation,[],[f4])).
% 1.85/0.61  fof(f4,axiom,(
% 1.85/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.85/0.61  fof(f133,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X1),X0) | k1_setfam_1(k2_tarski(X1,X0)) = X1) )),
% 1.85/0.61    inference(duplicate_literal_removal,[],[f132])).
% 1.85/0.61  fof(f132,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X1),X0) | k1_setfam_1(k2_tarski(X1,X0)) = X1 | k1_setfam_1(k2_tarski(X1,X0)) = X1) )),
% 1.85/0.61    inference(resolution,[],[f126,f62])).
% 1.85/0.61  fof(f126,plain,(
% 1.85/0.61    ( ! [X4,X5] : (sP0(X5,X4,X4) | ~r2_hidden(sK4(X5,X4,X4),X5) | k1_setfam_1(k2_tarski(X4,X5)) = X4) )),
% 1.85/0.61    inference(resolution,[],[f123,f111])).
% 1.85/0.61  fof(f123,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X1),X1) | k1_setfam_1(k2_tarski(X1,X0)) = X1 | ~r2_hidden(sK4(X0,X1,X1),X0)) )),
% 1.85/0.61    inference(duplicate_literal_removal,[],[f122])).
% 1.85/0.61  fof(f122,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X1),X0) | k1_setfam_1(k2_tarski(X1,X0)) = X1 | ~r2_hidden(sK4(X0,X1,X1),X1) | k1_setfam_1(k2_tarski(X1,X0)) = X1) )),
% 1.85/0.61    inference(resolution,[],[f116,f62])).
% 1.85/0.61  fof(f116,plain,(
% 1.85/0.61    ( ! [X6,X7] : (sP0(X6,X7,X7) | ~r2_hidden(sK4(X6,X7,X7),X6) | k1_setfam_1(k2_tarski(X7,X6)) = X7 | ~r2_hidden(sK4(X6,X7,X7),X7)) )),
% 1.85/0.61    inference(resolution,[],[f113,f111])).
% 1.85/0.61  fof(f113,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X1,X0)) = X2) )),
% 1.85/0.61    inference(resolution,[],[f58,f62])).
% 1.85/0.61  fof(f58,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f34])).
% 1.85/0.61  fof(f174,plain,(
% 1.85/0.61    spl5_5),
% 1.85/0.61    inference(avatar_contradiction_clause,[],[f173])).
% 1.85/0.61  fof(f173,plain,(
% 1.85/0.61    $false | spl5_5),
% 1.85/0.61    inference(resolution,[],[f168,f70])).
% 1.85/0.61  fof(f168,plain,(
% 1.85/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1))) | spl5_5),
% 1.85/0.61    inference(avatar_component_clause,[],[f166])).
% 1.85/0.61  fof(f166,plain,(
% 1.85/0.61    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.85/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.85/0.61  fof(f172,plain,(
% 1.85/0.61    ~spl5_5 | spl5_6 | ~spl5_4),
% 1.85/0.61    inference(avatar_split_clause,[],[f164,f151,f170,f166])).
% 1.85/0.61  fof(f151,plain,(
% 1.85/0.61    spl5_4 <=> ! [X1,X0] : (k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,X1)) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))))),
% 1.85/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.85/0.61  fof(f164,plain,(
% 1.85/0.61    ( ! [X0] : (k2_pre_topc(sK1,k1_setfam_1(k2_tarski(X0,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(sK3,k2_pre_topc(sK1,X0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1)))) ) | ~spl5_4),
% 1.85/0.61    inference(forward_demodulation,[],[f163,f75])).
% 1.85/0.61  fof(f163,plain,(
% 1.85/0.61    ( ! [X0] : (k2_pre_topc(sK1,k1_setfam_1(k2_tarski(X0,sK3))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(k2_pre_topc(sK1,X0),sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1)))) ) | ~spl5_4),
% 1.85/0.61    inference(forward_demodulation,[],[f162,f88])).
% 1.85/0.61  fof(f88,plain,(
% 1.85/0.61    ( ! [X1] : (k9_subset_1(k2_struct_0(sK1),sK3,X1) = k1_setfam_1(k2_tarski(X1,sK3))) )),
% 1.85/0.61    inference(backward_demodulation,[],[f81,f84])).
% 1.85/0.61  fof(f84,plain,(
% 1.85/0.61    ( ! [X1] : (k9_subset_1(k2_struct_0(sK1),X1,sK3) = k1_setfam_1(k2_tarski(X1,sK3))) )),
% 1.85/0.61    inference(resolution,[],[f61,f70])).
% 1.85/0.61  fof(f81,plain,(
% 1.85/0.61    ( ! [X1] : (k9_subset_1(k2_struct_0(sK1),X1,sK3) = k9_subset_1(k2_struct_0(sK1),sK3,X1)) )),
% 1.85/0.61    inference(resolution,[],[f52,f70])).
% 1.85/0.61  fof(f162,plain,(
% 1.85/0.61    ( ! [X0] : (k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k1_setfam_1(k2_tarski(X0,sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1)))) ) | ~spl5_4),
% 1.85/0.61    inference(forward_demodulation,[],[f161,f88])).
% 1.85/0.61  fof(f161,plain,(
% 1.85/0.61    ( ! [X0] : (k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),sK3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK1)))) ) | ~spl5_4),
% 1.85/0.61    inference(resolution,[],[f152,f41])).
% 1.85/0.61  fof(f41,plain,(
% 1.85/0.61    v3_pre_topc(sK3,sK1)),
% 1.85/0.61    inference(cnf_transformation,[],[f28])).
% 1.85/0.61  fof(f152,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~v3_pre_topc(X0,sK1) | k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))) ) | ~spl5_4),
% 1.85/0.61    inference(avatar_component_clause,[],[f151])).
% 1.85/0.61  fof(f155,plain,(
% 1.85/0.61    spl5_3),
% 1.85/0.61    inference(avatar_contradiction_clause,[],[f154])).
% 1.85/0.61  fof(f154,plain,(
% 1.85/0.61    $false | spl5_3),
% 1.85/0.61    inference(resolution,[],[f149,f37])).
% 1.85/0.61  fof(f149,plain,(
% 1.85/0.61    ~l1_pre_topc(sK1) | spl5_3),
% 1.85/0.61    inference(avatar_component_clause,[],[f147])).
% 1.85/0.61  fof(f147,plain,(
% 1.85/0.61    spl5_3 <=> l1_pre_topc(sK1)),
% 1.85/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.85/0.61  fof(f153,plain,(
% 1.85/0.61    ~spl5_3 | spl5_4),
% 1.85/0.61    inference(avatar_split_clause,[],[f145,f151,f147])).
% 1.85/0.61  fof(f145,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(k2_struct_0(sK1),X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | ~l1_pre_topc(sK1)) )),
% 1.85/0.61    inference(forward_demodulation,[],[f144,f68])).
% 1.85/0.61  fof(f144,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,X1))) )),
% 1.85/0.61    inference(forward_demodulation,[],[f143,f68])).
% 1.85/0.61  fof(f143,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,X1))) )),
% 1.85/0.61    inference(forward_demodulation,[],[f142,f68])).
% 1.85/0.61  fof(f142,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~v3_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,k2_pre_topc(sK1,X1))) = k2_pre_topc(sK1,k9_subset_1(u1_struct_0(sK1),X0,X1))) )),
% 1.85/0.61    inference(resolution,[],[f47,f36])).
% 1.85/0.61  fof(f36,plain,(
% 1.85/0.61    v2_pre_topc(sK1)),
% 1.85/0.61    inference(cnf_transformation,[],[f28])).
% 1.85/0.61  fof(f47,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) )),
% 1.85/0.61    inference(cnf_transformation,[],[f19])).
% 1.85/0.61  fof(f19,plain,(
% 1.85/0.61    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.85/0.61    inference(flattening,[],[f18])).
% 1.85/0.61  fof(f18,plain,(
% 1.85/0.61    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.85/0.61    inference(ennf_transformation,[],[f10])).
% 1.85/0.61  fof(f10,axiom,(
% 1.85/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).
% 1.85/0.61  fof(f106,plain,(
% 1.85/0.61    spl5_2),
% 1.85/0.61    inference(avatar_contradiction_clause,[],[f105])).
% 1.85/0.61  fof(f105,plain,(
% 1.85/0.61    $false | spl5_2),
% 1.85/0.61    inference(resolution,[],[f103,f69])).
% 1.85/0.61  fof(f103,plain,(
% 1.85/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) | spl5_2),
% 1.85/0.61    inference(avatar_component_clause,[],[f101])).
% 1.85/0.61  fof(f101,plain,(
% 1.85/0.61    spl5_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.85/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.85/0.61  fof(f104,plain,(
% 1.85/0.61    spl5_1 | ~spl5_2),
% 1.85/0.61    inference(avatar_split_clause,[],[f95,f101,f97])).
% 1.85/0.61  fof(f95,plain,(
% 1.85/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) | k2_struct_0(sK1) = k2_pre_topc(sK1,sK2)),
% 1.85/0.61    inference(resolution,[],[f94,f39])).
% 1.85/0.61  fof(f39,plain,(
% 1.85/0.61    v1_tops_1(sK2,sK1)),
% 1.85/0.61    inference(cnf_transformation,[],[f28])).
% 1.85/0.61  fof(f94,plain,(
% 1.85/0.61    ( ! [X0] : (~v1_tops_1(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | k2_struct_0(sK1) = k2_pre_topc(sK1,X0)) )),
% 1.85/0.61    inference(forward_demodulation,[],[f93,f68])).
% 1.85/0.61  fof(f93,plain,(
% 1.85/0.61    ( ! [X0] : (~v1_tops_1(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_struct_0(sK1) = k2_pre_topc(sK1,X0)) )),
% 1.85/0.61    inference(resolution,[],[f45,f37])).
% 1.85/0.61  fof(f45,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f29])).
% 1.85/0.61  fof(f29,plain,(
% 1.85/0.61    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.85/0.61    inference(nnf_transformation,[],[f17])).
% 1.85/0.61  fof(f17,plain,(
% 1.85/0.61    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.85/0.61    inference(ennf_transformation,[],[f9])).
% 1.85/0.61  fof(f9,axiom,(
% 1.85/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.85/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 1.85/0.61  % SZS output end Proof for theBenchmark
% 1.85/0.61  % (10892)------------------------------
% 1.85/0.61  % (10892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.61  % (10892)Termination reason: Refutation
% 1.85/0.61  
% 1.85/0.61  % (10892)Memory used [KB]: 6524
% 1.85/0.61  % (10892)Time elapsed: 0.187 s
% 1.85/0.61  % (10892)------------------------------
% 1.85/0.61  % (10892)------------------------------
% 1.85/0.62  % (10879)Success in time 0.24 s
%------------------------------------------------------------------------------
