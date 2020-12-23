%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:43 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  137 (15590 expanded)
%              Number of leaves         :   21 (4755 expanded)
%              Depth                    :   29
%              Number of atoms          :  498 (55667 expanded)
%              Number of equality atoms :  119 (20293 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1893,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f1182,f1892])).

fof(f1892,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f1891])).

fof(f1891,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f1890,f1727])).

fof(f1727,plain,
    ( ~ r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f1725,f104])).

fof(f104,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl8_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1725,plain,
    ( ~ r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f1313,f203])).

fof(f203,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X12,X11)
      | ~ r2_hidden(X12,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X11)) ) ),
    inference(superposition,[],[f85,f121])).

fof(f121,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f110,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f110,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f40,f41,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).

fof(f26,plain,
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
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

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

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1313,plain,
    ( r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),sK1)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f1312,f1183])).

fof(f1183,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f114,f41,f101,f90])).

fof(f90,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP4(X0) ) ),
    inference(cnf_transformation,[],[f90_D])).

fof(f90_D,plain,(
    ! [X0] :
      ( ! [X2] :
          ( v3_pre_topc(X2,X0)
          | k1_tops_1(X0,X2) != X2
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    <=> ~ sP4(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f101,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl8_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f114,plain,(
    ~ sP4(sK0) ),
    inference(unit_resulting_resolution,[],[f40,f39,f111,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP4(X0)
      | sP5 ) ),
    inference(cnf_transformation,[],[f92_D])).

fof(f92_D,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ sP4(X0) )
  <=> ~ sP5 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f111,plain,(
    ~ sP5 ),
    inference(unit_resulting_resolution,[],[f40,f41,f93])).

fof(f93,plain,(
    ! [X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sP5 ) ),
    inference(general_splitting,[],[f91,f92_D])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP4(X0) ) ),
    inference(general_splitting,[],[f48,f90_D])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
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

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f1312,plain,
    ( r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),sK1)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(factoring,[],[f837])).

fof(f837,plain,(
    ! [X4] :
      ( r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X4),sK1)
      | k1_tops_1(sK0,sK1) = X4
      | r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X4),X4) ) ),
    inference(forward_demodulation,[],[f807,f826])).

fof(f826,plain,(
    k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f792,f819])).

fof(f819,plain,(
    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f818,f108])).

fof(f108,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f45])).

fof(f45,plain,(
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

fof(f818,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f802,f792])).

fof(f802,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f113,f771])).

fof(f771,plain,(
    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f713,f108])).

fof(f713,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(backward_demodulation,[],[f178,f711])).

fof(f711,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(subsumption_resolution,[],[f702,f273])).

fof(f273,plain,(
    ! [X6,X5] :
      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X5))) = X6
      | ~ r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5),X6),k7_subset_1(u1_struct_0(sK0),sK1,X5))
      | ~ r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5),X6),X6) ) ),
    inference(subsumption_resolution,[],[f251,f140])).

fof(f140,plain,(
    ! [X14,X13] :
      ( r2_hidden(X14,sK1)
      | ~ r2_hidden(X14,k7_subset_1(u1_struct_0(sK0),sK1,X13)) ) ),
    inference(superposition,[],[f86,f113])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f251,plain,(
    ! [X6,X5] :
      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X5))) = X6
      | ~ r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5),X6),k7_subset_1(u1_struct_0(sK0),sK1,X5))
      | ~ r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5),X6),sK1)
      | ~ r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5),X6),X6) ) ),
    inference(superposition,[],[f175,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f66,f50])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
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
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
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
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f175,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(superposition,[],[f142,f142])).

fof(f142,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1)) ),
    inference(forward_demodulation,[],[f128,f113])).

fof(f128,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1)))) ),
    inference(superposition,[],[f113,f70])).

fof(f70,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f52,f50,f67,f67])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f702,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0),k7_subset_1(u1_struct_0(sK0),sK1,X0)),k7_subset_1(u1_struct_0(sK0),sK1,X0))
      | k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0))) ) ),
    inference(factoring,[],[f250])).

fof(f250,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X3),X4),k7_subset_1(u1_struct_0(sK0),sK1,X3))
      | k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X3))) = X4
      | r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X3),X4),X4) ) ),
    inference(superposition,[],[f175,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f65,f50])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f178,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ),
    inference(backward_demodulation,[],[f133,f175])).

fof(f133,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) ),
    inference(superposition,[],[f70,f113])).

fof(f113,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f41,f71])).

fof(f792,plain,(
    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f737,f771])).

fof(f737,plain,(
    k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f508,f732])).

fof(f732,plain,(
    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f721,f173])).

fof(f173,plain,(
    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f142,f108])).

fof(f721,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))) ),
    inference(backward_demodulation,[],[f247,f711])).

fof(f247,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))) ),
    inference(superposition,[],[f175,f173])).

fof(f508,plain,(
    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))))) ),
    inference(superposition,[],[f178,f247])).

fof(f807,plain,(
    ! [X4] :
      ( k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) = X4
      | r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X4),sK1)
      | r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X4),X4) ) ),
    inference(superposition,[],[f74,f771])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1890,plain,
    ( r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f1183,f1313,f1313,f835])).

fof(f835,plain,(
    ! [X2] :
      ( r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),k2_tops_1(sK0,sK1))
      | k1_tops_1(sK0,sK1) = X2
      | ~ r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),sK1)
      | ~ r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),X2) ) ),
    inference(forward_demodulation,[],[f805,f826])).

fof(f805,plain,(
    ! [X2] :
      ( k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) = X2
      | r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),k2_tops_1(sK0,sK1))
      | ~ r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),sK1)
      | ~ r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f72,f771])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1182,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f1181,f99])).

fof(f1181,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f43,f1180])).

fof(f1180,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1179,f115])).

fof(f115,plain,(
    sP7 ),
    inference(unit_resulting_resolution,[],[f40,f39,f112,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0)
      | sP7 ) ),
    inference(cnf_transformation,[],[f96_D])).

fof(f96_D,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ sP6(X0) )
  <=> ~ sP7 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f112,plain,(
    sP6(sK0) ),
    inference(unit_resulting_resolution,[],[f41,f94])).

fof(f94,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP6(X0) ) ),
    inference(cnf_transformation,[],[f94_D])).

fof(f94_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    <=> ~ sP6(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f1179,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ sP7 ),
    inference(subsumption_resolution,[],[f1178,f40])).

fof(f1178,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ sP7 ),
    inference(subsumption_resolution,[],[f144,f41])).

fof(f144,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ sP7 ),
    inference(superposition,[],[f109,f97])).

fof(f97,plain,(
    ! [X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sP7 ) ),
    inference(general_splitting,[],[f95,f96_D])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0) ) ),
    inference(general_splitting,[],[f47,f94_D])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f109,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f46])).

fof(f46,plain,(
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

fof(f43,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f42,f103,f99])).

fof(f42,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (13428)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (13452)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.49  % (13443)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.50  % (13436)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (13424)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (13427)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (13433)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (13434)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (13431)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (13432)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (13448)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (13442)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (13440)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (13425)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (13426)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (13429)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (13450)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (13446)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (13441)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (13439)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (13446)Refutation not found, incomplete strategy% (13446)------------------------------
% 0.20/0.54  % (13446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13439)Refutation not found, incomplete strategy% (13439)------------------------------
% 0.20/0.54  % (13439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13439)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13439)Memory used [KB]: 6140
% 0.20/0.54  % (13439)Time elapsed: 0.004 s
% 0.20/0.54  % (13439)------------------------------
% 0.20/0.54  % (13439)------------------------------
% 0.20/0.54  % (13446)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13446)Memory used [KB]: 10746
% 0.20/0.54  % (13446)Time elapsed: 0.118 s
% 0.20/0.54  % (13446)------------------------------
% 0.20/0.54  % (13446)------------------------------
% 0.20/0.54  % (13438)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (13441)Refutation not found, incomplete strategy% (13441)------------------------------
% 0.20/0.54  % (13441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13441)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13441)Memory used [KB]: 10618
% 0.20/0.54  % (13441)Time elapsed: 0.135 s
% 0.20/0.54  % (13441)------------------------------
% 0.20/0.54  % (13441)------------------------------
% 0.20/0.55  % (13437)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (13435)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (13451)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.51/0.55  % (13447)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.56  % (13444)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.56  % (13445)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.51/0.56  % (13430)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.51/0.57  % (13449)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.51/0.57  % (13453)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.04/0.65  % (13455)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.23/0.67  % (13456)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.23/0.71  % (13454)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.70/0.73  % (13450)Refutation found. Thanks to Tanya!
% 2.70/0.73  % SZS status Theorem for theBenchmark
% 2.70/0.73  % SZS output start Proof for theBenchmark
% 2.70/0.73  fof(f1893,plain,(
% 2.70/0.73    $false),
% 2.70/0.73    inference(avatar_sat_refutation,[],[f107,f1182,f1892])).
% 2.70/0.73  fof(f1892,plain,(
% 2.70/0.73    spl8_1 | ~spl8_2),
% 2.70/0.73    inference(avatar_contradiction_clause,[],[f1891])).
% 2.70/0.73  fof(f1891,plain,(
% 2.70/0.73    $false | (spl8_1 | ~spl8_2)),
% 2.70/0.73    inference(subsumption_resolution,[],[f1890,f1727])).
% 2.70/0.73  fof(f1727,plain,(
% 2.70/0.73    ~r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | (spl8_1 | ~spl8_2)),
% 2.70/0.73    inference(forward_demodulation,[],[f1725,f104])).
% 2.70/0.73  fof(f104,plain,(
% 2.70/0.73    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl8_2),
% 2.70/0.73    inference(avatar_component_clause,[],[f103])).
% 2.70/0.73  fof(f103,plain,(
% 2.70/0.73    spl8_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.70/0.73    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.70/0.73  fof(f1725,plain,(
% 2.70/0.73    ~r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)) | spl8_1),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f1313,f203])).
% 2.70/0.73  fof(f203,plain,(
% 2.70/0.73    ( ! [X12,X11] : (~r2_hidden(X12,X11) | ~r2_hidden(X12,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X11))) )),
% 2.70/0.73    inference(superposition,[],[f85,f121])).
% 2.70/0.73  fof(f121,plain,(
% 2.70/0.73    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X0)))) )),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f110,f71])).
% 2.70/0.73  fof(f71,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.70/0.73    inference(definition_unfolding,[],[f54,f67])).
% 2.70/0.73  fof(f67,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.70/0.73    inference(definition_unfolding,[],[f51,f50])).
% 2.70/0.73  fof(f50,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f8])).
% 2.70/0.73  fof(f8,axiom,(
% 2.70/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.70/0.73  fof(f51,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f4])).
% 2.70/0.73  fof(f4,axiom,(
% 2.70/0.73    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.70/0.73  fof(f54,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f23])).
% 2.70/0.73  fof(f23,plain,(
% 2.70/0.73    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.70/0.73    inference(ennf_transformation,[],[f7])).
% 2.70/0.73  fof(f7,axiom,(
% 2.70/0.73    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.70/0.73  fof(f110,plain,(
% 2.70/0.73    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f40,f41,f53])).
% 2.70/0.73  fof(f53,plain,(
% 2.70/0.73    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f22])).
% 2.70/0.73  fof(f22,plain,(
% 2.70/0.73    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.70/0.73    inference(flattening,[],[f21])).
% 2.70/0.73  fof(f21,plain,(
% 2.70/0.73    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.70/0.73    inference(ennf_transformation,[],[f9])).
% 2.70/0.73  fof(f9,axiom,(
% 2.70/0.73    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.70/0.73  fof(f41,plain,(
% 2.70/0.73    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.70/0.73    inference(cnf_transformation,[],[f28])).
% 2.70/0.73  fof(f28,plain,(
% 2.70/0.73    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.70/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).
% 2.70/0.73  fof(f26,plain,(
% 2.70/0.73    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.70/0.73    introduced(choice_axiom,[])).
% 2.70/0.73  fof(f27,plain,(
% 2.70/0.73    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.70/0.73    introduced(choice_axiom,[])).
% 2.70/0.73  fof(f25,plain,(
% 2.70/0.73    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.70/0.73    inference(flattening,[],[f24])).
% 2.70/0.73  fof(f24,plain,(
% 2.70/0.73    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.70/0.73    inference(nnf_transformation,[],[f16])).
% 2.70/0.73  fof(f16,plain,(
% 2.70/0.73    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.70/0.73    inference(flattening,[],[f15])).
% 2.70/0.73  fof(f15,plain,(
% 2.70/0.73    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.70/0.73    inference(ennf_transformation,[],[f14])).
% 2.70/0.73  fof(f14,negated_conjecture,(
% 2.70/0.73    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.70/0.73    inference(negated_conjecture,[],[f13])).
% 2.70/0.73  fof(f13,conjecture,(
% 2.70/0.73    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.70/0.73  fof(f40,plain,(
% 2.70/0.73    l1_pre_topc(sK0)),
% 2.70/0.73    inference(cnf_transformation,[],[f28])).
% 2.70/0.73  fof(f85,plain,(
% 2.70/0.73    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 2.70/0.73    inference(equality_resolution,[],[f76])).
% 2.70/0.73  fof(f76,plain,(
% 2.70/0.73    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.70/0.73    inference(definition_unfolding,[],[f56,f67])).
% 2.70/0.73  fof(f56,plain,(
% 2.70/0.73    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.70/0.73    inference(cnf_transformation,[],[f33])).
% 2.70/0.73  fof(f33,plain,(
% 2.70/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 2.70/0.73  fof(f32,plain,(
% 2.70/0.73    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.70/0.73    introduced(choice_axiom,[])).
% 2.70/0.73  fof(f31,plain,(
% 2.70/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.73    inference(rectify,[],[f30])).
% 2.70/0.73  fof(f30,plain,(
% 2.70/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.73    inference(flattening,[],[f29])).
% 2.70/0.73  fof(f29,plain,(
% 2.70/0.73    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.70/0.73    inference(nnf_transformation,[],[f3])).
% 2.70/0.73  fof(f3,axiom,(
% 2.70/0.73    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.70/0.73  fof(f1313,plain,(
% 2.70/0.73    r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),sK1) | spl8_1),
% 2.70/0.73    inference(subsumption_resolution,[],[f1312,f1183])).
% 2.70/0.73  fof(f1183,plain,(
% 2.70/0.73    sK1 != k1_tops_1(sK0,sK1) | spl8_1),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f114,f41,f101,f90])).
% 2.70/0.73  fof(f90,plain,(
% 2.70/0.73    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP4(X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f90_D])).
% 2.70/0.73  fof(f90_D,plain,(
% 2.70/0.73    ( ! [X0] : (( ! [X2] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) <=> ~sP4(X0)) )),
% 2.70/0.73    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 2.70/0.73  fof(f101,plain,(
% 2.70/0.73    ~v3_pre_topc(sK1,sK0) | spl8_1),
% 2.70/0.73    inference(avatar_component_clause,[],[f99])).
% 2.70/0.73  fof(f99,plain,(
% 2.70/0.73    spl8_1 <=> v3_pre_topc(sK1,sK0)),
% 2.70/0.73    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.70/0.73  fof(f114,plain,(
% 2.70/0.73    ~sP4(sK0)),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f40,f39,f111,f92])).
% 2.70/0.73  fof(f92,plain,(
% 2.70/0.73    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP4(X0) | sP5) )),
% 2.70/0.73    inference(cnf_transformation,[],[f92_D])).
% 2.70/0.73  fof(f92_D,plain,(
% 2.70/0.73    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP4(X0)) ) <=> ~sP5),
% 2.70/0.73    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 2.70/0.73  fof(f111,plain,(
% 2.70/0.73    ~sP5),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f40,f41,f93])).
% 2.70/0.73  fof(f93,plain,(
% 2.70/0.73    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sP5) )),
% 2.70/0.73    inference(general_splitting,[],[f91,f92_D])).
% 2.70/0.73  fof(f91,plain,(
% 2.70/0.73    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP4(X0)) )),
% 2.70/0.73    inference(general_splitting,[],[f48,f90_D])).
% 2.70/0.73  fof(f48,plain,(
% 2.70/0.73    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f20])).
% 2.70/0.73  fof(f20,plain,(
% 2.70/0.73    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.70/0.73    inference(flattening,[],[f19])).
% 2.70/0.73  fof(f19,plain,(
% 2.70/0.73    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.70/0.73    inference(ennf_transformation,[],[f11])).
% 2.70/0.73  fof(f11,axiom,(
% 2.70/0.73    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 2.70/0.73  fof(f39,plain,(
% 2.70/0.73    v2_pre_topc(sK0)),
% 2.70/0.73    inference(cnf_transformation,[],[f28])).
% 2.70/0.73  fof(f1312,plain,(
% 2.70/0.73    r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),sK1) | sK1 = k1_tops_1(sK0,sK1)),
% 2.70/0.73    inference(factoring,[],[f837])).
% 2.70/0.73  fof(f837,plain,(
% 2.70/0.73    ( ! [X4] : (r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X4),sK1) | k1_tops_1(sK0,sK1) = X4 | r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X4),X4)) )),
% 2.70/0.73    inference(forward_demodulation,[],[f807,f826])).
% 2.70/0.73  fof(f826,plain,(
% 2.70/0.73    k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 2.70/0.73    inference(backward_demodulation,[],[f792,f819])).
% 2.70/0.73  fof(f819,plain,(
% 2.70/0.73    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))),
% 2.70/0.73    inference(forward_demodulation,[],[f818,f108])).
% 2.70/0.73  fof(f108,plain,(
% 2.70/0.73    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f40,f41,f45])).
% 2.70/0.73  fof(f45,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f17])).
% 2.70/0.73  fof(f17,plain,(
% 2.70/0.73    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.73    inference(ennf_transformation,[],[f12])).
% 2.70/0.73  fof(f12,axiom,(
% 2.70/0.73    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.70/0.73  fof(f818,plain,(
% 2.70/0.73    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))),
% 2.70/0.73    inference(forward_demodulation,[],[f802,f792])).
% 2.70/0.73  fof(f802,plain,(
% 2.70/0.73    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 2.70/0.73    inference(superposition,[],[f113,f771])).
% 2.70/0.73  fof(f771,plain,(
% 2.70/0.73    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.70/0.73    inference(superposition,[],[f713,f108])).
% 2.70/0.73  fof(f713,plain,(
% 2.70/0.73    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) )),
% 2.70/0.73    inference(backward_demodulation,[],[f178,f711])).
% 2.70/0.73  fof(f711,plain,(
% 2.70/0.73    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 2.70/0.73    inference(subsumption_resolution,[],[f702,f273])).
% 2.70/0.73  fof(f273,plain,(
% 2.70/0.73    ( ! [X6,X5] : (k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X5))) = X6 | ~r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5),X6),k7_subset_1(u1_struct_0(sK0),sK1,X5)) | ~r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5),X6),X6)) )),
% 2.70/0.73    inference(subsumption_resolution,[],[f251,f140])).
% 2.70/0.73  fof(f140,plain,(
% 2.70/0.73    ( ! [X14,X13] : (r2_hidden(X14,sK1) | ~r2_hidden(X14,k7_subset_1(u1_struct_0(sK0),sK1,X13))) )),
% 2.70/0.73    inference(superposition,[],[f86,f113])).
% 2.70/0.73  fof(f86,plain,(
% 2.70/0.73    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 2.70/0.73    inference(equality_resolution,[],[f77])).
% 2.70/0.73  fof(f77,plain,(
% 2.70/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.70/0.73    inference(definition_unfolding,[],[f55,f67])).
% 2.70/0.73  fof(f55,plain,(
% 2.70/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.70/0.73    inference(cnf_transformation,[],[f33])).
% 2.70/0.73  fof(f251,plain,(
% 2.70/0.73    ( ! [X6,X5] : (k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X5))) = X6 | ~r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5),X6),k7_subset_1(u1_struct_0(sK0),sK1,X5)) | ~r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5),X6),sK1) | ~r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X5),X6),X6)) )),
% 2.70/0.73    inference(superposition,[],[f175,f78])).
% 2.70/0.73  fof(f78,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f66,f50])).
% 2.70/0.73  fof(f66,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f38])).
% 2.70/0.73  fof(f38,plain,(
% 2.70/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.70/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 2.70/0.73  fof(f37,plain,(
% 2.70/0.73    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.70/0.73    introduced(choice_axiom,[])).
% 2.70/0.73  fof(f36,plain,(
% 2.70/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.70/0.73    inference(rectify,[],[f35])).
% 2.70/0.73  fof(f35,plain,(
% 2.70/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.70/0.73    inference(flattening,[],[f34])).
% 2.70/0.73  fof(f34,plain,(
% 2.70/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.70/0.73    inference(nnf_transformation,[],[f2])).
% 2.70/0.73  fof(f2,axiom,(
% 2.70/0.73    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.70/0.73  fof(f175,plain,(
% 2.70/0.73    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 2.70/0.73    inference(superposition,[],[f142,f142])).
% 2.70/0.73  fof(f142,plain,(
% 2.70/0.73    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))) )),
% 2.70/0.73    inference(forward_demodulation,[],[f128,f113])).
% 2.70/0.73  fof(f128,plain,(
% 2.70/0.73    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1))))) )),
% 2.70/0.73    inference(superposition,[],[f113,f70])).
% 2.70/0.73  fof(f70,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 2.70/0.73    inference(definition_unfolding,[],[f52,f50,f67,f67])).
% 2.70/0.73  fof(f52,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f6])).
% 2.70/0.73  fof(f6,axiom,(
% 2.70/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.70/0.73  fof(f702,plain,(
% 2.70/0.73    ( ! [X0] : (r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0),k7_subset_1(u1_struct_0(sK0),sK1,X0)),k7_subset_1(u1_struct_0(sK0),sK1,X0)) | k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 2.70/0.73    inference(factoring,[],[f250])).
% 2.70/0.73  fof(f250,plain,(
% 2.70/0.73    ( ! [X4,X3] : (r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X3),X4),k7_subset_1(u1_struct_0(sK0),sK1,X3)) | k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X3))) = X4 | r2_hidden(sK3(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X3),X4),X4)) )),
% 2.70/0.73    inference(superposition,[],[f175,f79])).
% 2.70/0.73  fof(f79,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f65,f50])).
% 2.70/0.73  fof(f65,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f38])).
% 2.70/0.73  fof(f178,plain,(
% 2.70/0.73    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0))))) )),
% 2.70/0.73    inference(backward_demodulation,[],[f133,f175])).
% 2.70/0.73  fof(f133,plain,(
% 2.70/0.73    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))))) )),
% 2.70/0.73    inference(superposition,[],[f70,f113])).
% 2.70/0.73  fof(f113,plain,(
% 2.70/0.73    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f41,f71])).
% 2.70/0.73  fof(f792,plain,(
% 2.70/0.73    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 2.70/0.73    inference(backward_demodulation,[],[f737,f771])).
% 2.70/0.73  fof(f737,plain,(
% 2.70/0.73    k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))),
% 2.70/0.73    inference(backward_demodulation,[],[f508,f732])).
% 2.70/0.73  fof(f732,plain,(
% 2.70/0.73    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))))),
% 2.70/0.73    inference(forward_demodulation,[],[f721,f173])).
% 2.70/0.73  fof(f173,plain,(
% 2.70/0.73    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.70/0.73    inference(superposition,[],[f142,f108])).
% 2.70/0.73  fof(f721,plain,(
% 2.70/0.73    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))))),
% 2.70/0.73    inference(backward_demodulation,[],[f247,f711])).
% 2.70/0.73  fof(f247,plain,(
% 2.70/0.73    k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))))),
% 2.70/0.73    inference(superposition,[],[f175,f173])).
% 2.70/0.73  fof(f508,plain,(
% 2.70/0.73    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))))),
% 2.70/0.73    inference(superposition,[],[f178,f247])).
% 2.70/0.73  fof(f807,plain,(
% 2.70/0.73    ( ! [X4] : (k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) = X4 | r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X4),sK1) | r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X4),X4)) )),
% 2.70/0.73    inference(superposition,[],[f74,f771])).
% 2.70/0.73  fof(f74,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f58,f67])).
% 2.70/0.73  fof(f58,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f33])).
% 2.70/0.73  fof(f1890,plain,(
% 2.70/0.73    r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | spl8_1),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f1183,f1313,f1313,f835])).
% 2.70/0.73  fof(f835,plain,(
% 2.70/0.73    ( ! [X2] : (r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),k2_tops_1(sK0,sK1)) | k1_tops_1(sK0,sK1) = X2 | ~r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),sK1) | ~r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),X2)) )),
% 2.70/0.73    inference(forward_demodulation,[],[f805,f826])).
% 2.70/0.73  fof(f805,plain,(
% 2.70/0.73    ( ! [X2] : (k5_xboole_0(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))) = X2 | r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),k2_tops_1(sK0,sK1)) | ~r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),sK1) | ~r2_hidden(sK2(sK1,k2_tops_1(sK0,sK1),X2),X2)) )),
% 2.70/0.73    inference(superposition,[],[f72,f771])).
% 2.70/0.73  fof(f72,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f60,f67])).
% 2.70/0.73  fof(f60,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f33])).
% 2.70/0.73  fof(f1182,plain,(
% 2.70/0.73    ~spl8_1),
% 2.70/0.73    inference(avatar_split_clause,[],[f1181,f99])).
% 2.70/0.73  fof(f1181,plain,(
% 2.70/0.73    ~v3_pre_topc(sK1,sK0)),
% 2.70/0.73    inference(global_subsumption,[],[f43,f1180])).
% 2.70/0.73  fof(f1180,plain,(
% 2.70/0.73    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.70/0.73    inference(subsumption_resolution,[],[f1179,f115])).
% 2.70/0.73  fof(f115,plain,(
% 2.70/0.73    sP7),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f40,f39,f112,f96])).
% 2.70/0.73  fof(f96,plain,(
% 2.70/0.73    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0) | sP7) )),
% 2.70/0.73    inference(cnf_transformation,[],[f96_D])).
% 2.70/0.73  fof(f96_D,plain,(
% 2.70/0.73    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0)) ) <=> ~sP7),
% 2.70/0.73    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 2.70/0.73  fof(f112,plain,(
% 2.70/0.73    sP6(sK0)),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f41,f94])).
% 2.70/0.73  fof(f94,plain,(
% 2.70/0.73    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP6(X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f94_D])).
% 2.70/0.73  fof(f94_D,plain,(
% 2.70/0.73    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) <=> ~sP6(X0)) )),
% 2.70/0.73    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 2.70/0.73  fof(f1179,plain,(
% 2.70/0.73    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0) | ~sP7),
% 2.70/0.73    inference(subsumption_resolution,[],[f1178,f40])).
% 2.70/0.73  fof(f1178,plain,(
% 2.70/0.73    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~sP7),
% 2.70/0.73    inference(subsumption_resolution,[],[f144,f41])).
% 2.70/0.73  fof(f144,plain,(
% 2.70/0.73    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~sP7),
% 2.70/0.73    inference(superposition,[],[f109,f97])).
% 2.70/0.73  fof(f97,plain,(
% 2.70/0.73    ( ! [X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sP7) )),
% 2.70/0.73    inference(general_splitting,[],[f95,f96_D])).
% 2.70/0.73  fof(f95,plain,(
% 2.70/0.73    ( ! [X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0)) )),
% 2.70/0.73    inference(general_splitting,[],[f47,f94_D])).
% 2.70/0.73  fof(f47,plain,(
% 2.70/0.73    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f20])).
% 2.70/0.73  fof(f109,plain,(
% 2.70/0.73    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f40,f41,f46])).
% 2.70/0.73  fof(f46,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f18])).
% 2.70/0.73  fof(f18,plain,(
% 2.70/0.73    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.73    inference(ennf_transformation,[],[f10])).
% 2.70/0.73  fof(f10,axiom,(
% 2.70/0.73    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.70/0.73  fof(f43,plain,(
% 2.70/0.73    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.70/0.73    inference(cnf_transformation,[],[f28])).
% 2.70/0.73  fof(f107,plain,(
% 2.70/0.73    spl8_1 | spl8_2),
% 2.70/0.73    inference(avatar_split_clause,[],[f42,f103,f99])).
% 2.70/0.73  fof(f42,plain,(
% 2.70/0.73    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.70/0.73    inference(cnf_transformation,[],[f28])).
% 2.70/0.73  % SZS output end Proof for theBenchmark
% 2.70/0.73  % (13450)------------------------------
% 2.70/0.73  % (13450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.73  % (13450)Termination reason: Refutation
% 2.70/0.73  
% 2.70/0.73  % (13450)Memory used [KB]: 12153
% 2.70/0.73  % (13450)Time elapsed: 0.322 s
% 2.70/0.73  % (13450)------------------------------
% 2.70/0.73  % (13450)------------------------------
% 2.70/0.73  % (13423)Success in time 0.373 s
%------------------------------------------------------------------------------
