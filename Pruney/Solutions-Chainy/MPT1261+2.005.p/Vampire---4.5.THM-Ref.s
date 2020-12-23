%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:47 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  164 (5511 expanded)
%              Number of leaves         :   23 (1711 expanded)
%              Depth                    :   32
%              Number of atoms          :  350 (16889 expanded)
%              Number of equality atoms :  150 (6907 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f98,f1108,f1121,f1127])).

fof(f1127,plain,
    ( spl3_2
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f1126])).

fof(f1126,plain,
    ( $false
    | spl3_2
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f1122,f96])).

fof(f96,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1122,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f110,f1117])).

fof(f1117,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f1116])).

fof(f1116,plain,
    ( spl3_25
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f110,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f102,f49])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f102,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f50,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f1121,plain,
    ( spl3_25
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f1120,f90,f1116])).

fof(f90,plain,
    ( spl3_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1120,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f100,f49])).

fof(f100,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f1108,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f1107])).

fof(f1107,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f1106,f109])).

fof(f109,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f108,f49])).

fof(f108,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f107,f92])).

fof(f92,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f107,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f101,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f50,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1106,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f1102,f934])).

fof(f934,plain,(
    sK1 = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f245,f907])).

fof(f907,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f897,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f897,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k5_xboole_0(sK1,sK1))
      | k5_xboole_0(sK1,sK1) = X0 ) ),
    inference(resolution,[],[f893,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f893,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(sK1,sK1),X0) ),
    inference(subsumption_resolution,[],[f890,f53])).

fof(f890,plain,(
    ! [X0] :
      ( r1_tarski(k5_xboole_0(sK1,sK1),X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f84,f243])).

fof(f243,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))))) ),
    inference(superposition,[],[f82,f236])).

fof(f236,plain,(
    k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) = k5_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f231,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f231,plain,(
    k1_setfam_1(k2_tarski(sK1,k1_xboole_0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f222,f160])).

fof(f160,plain,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(superposition,[],[f105,f80])).

fof(f80,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f55,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f65,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f105,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,X1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1))) ),
    inference(resolution,[],[f50,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f76,f78])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f222,plain,(
    ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2)) ),
    inference(backward_demodulation,[],[f164,f221])).

fof(f221,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ),
    inference(forward_demodulation,[],[f217,f170])).

fof(f170,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2))) = k7_subset_1(u1_struct_0(sK0),sK1,X2) ),
    inference(forward_demodulation,[],[f162,f105])).

fof(f162,plain,(
    ! [X2] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X2))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2))) ),
    inference(superposition,[],[f105,f83])).

fof(f83,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1))))) ),
    inference(definition_unfolding,[],[f66,f78,f78,f61])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f217,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ),
    inference(superposition,[],[f169,f169])).

fof(f169,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1)) ),
    inference(forward_demodulation,[],[f161,f105])).

fof(f161,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1)))) ),
    inference(superposition,[],[f105,f82])).

fof(f164,plain,(
    ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2)))) ),
    inference(superposition,[],[f82,f105])).

fof(f82,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f64,f61,f78,f78])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f245,plain,(
    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f240,f160])).

fof(f240,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f158,f236])).

fof(f158,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) ),
    inference(superposition,[],[f105,f60])).

fof(f1102,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f867,f1093])).

fof(f1093,plain,(
    ! [X1] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1)) ),
    inference(superposition,[],[f1055,f82])).

fof(f1055,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ),
    inference(resolution,[],[f959,f88])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f959,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(forward_demodulation,[],[f958,f907])).

fof(f958,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_tarski(X0,k5_xboole_0(sK1,sK1)) ) ),
    inference(forward_demodulation,[],[f909,f907])).

fof(f909,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k5_xboole_0(sK1,sK1)
      | ~ r1_tarski(X0,k5_xboole_0(sK1,sK1)) ) ),
    inference(resolution,[],[f897,f84])).

fof(f867,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_xboole_0,k2_tops_1(sK0,sK1))))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f866,f335])).

fof(f335,plain,(
    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f331,f111])).

fof(f111,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f103,f49])).

fof(f103,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f50,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f331,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f117,f50])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1))) ) ),
    inference(resolution,[],[f106,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f77,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f106,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f99,f49])).

fof(f99,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f50,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f866,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_xboole_0,k2_tops_1(sK0,sK1))))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f865,f823])).

fof(f823,plain,(
    ! [X1] : k3_tarski(k2_tarski(sK1,X1)) = k3_tarski(k2_tarski(X1,sK1)) ),
    inference(superposition,[],[f767,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f63,f62,f78])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f767,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1)))) ),
    inference(superposition,[],[f444,f60])).

fof(f444,plain,(
    ! [X8] : k3_tarski(k2_tarski(sK1,X8)) = k5_xboole_0(sK1,k5_xboole_0(X8,k1_setfam_1(k2_tarski(sK1,X8)))) ),
    inference(superposition,[],[f81,f414])).

fof(f414,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k1_setfam_1(k2_tarski(X1,sK1)) ),
    inference(superposition,[],[f386,f222])).

fof(f386,plain,(
    ! [X8] : k1_setfam_1(k2_tarski(X8,sK1)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X8)) ),
    inference(forward_demodulation,[],[f385,f221])).

fof(f385,plain,(
    ! [X8] : k1_setfam_1(k2_tarski(X8,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X8)))) ),
    inference(forward_demodulation,[],[f379,f158])).

fof(f379,plain,(
    ! [X8] : k1_setfam_1(k2_tarski(X8,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X8,sK1)))))) ),
    inference(superposition,[],[f82,f354])).

fof(f354,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,sK1)) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(X0,sK1)))) ),
    inference(superposition,[],[f254,f60])).

fof(f254,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ),
    inference(forward_demodulation,[],[f250,f222])).

fof(f250,plain,(
    ! [X0] : k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ),
    inference(superposition,[],[f222,f170])).

fof(f865,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_xboole_0,k2_tops_1(sK0,sK1))))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f851,f812])).

fof(f812,plain,(
    k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(k1_xboole_0,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f808,f60])).

fof(f808,plain,(
    k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k1_xboole_0)) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f790,f307])).

fof(f307,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f118,f80])).

fof(f118,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X1) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1))) ),
    inference(resolution,[],[f106,f85])).

fof(f790,plain,(
    ! [X2] : k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2)) = k5_xboole_0(k2_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X2)) ),
    inference(backward_demodulation,[],[f311,f789])).

fof(f789,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0))) ),
    inference(forward_demodulation,[],[f785,f317])).

fof(f317,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X2) ),
    inference(forward_demodulation,[],[f309,f118])).

fof(f309,plain,(
    ! [X2] : k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2))) ),
    inference(superposition,[],[f118,f83])).

fof(f785,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0))) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0))) ),
    inference(superposition,[],[f316,f316])).

fof(f316,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X1)) ),
    inference(forward_demodulation,[],[f308,f118])).

fof(f308,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1)))) ),
    inference(superposition,[],[f118,f82])).

fof(f311,plain,(
    ! [X2] : k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2)) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X2)))) ),
    inference(superposition,[],[f82,f118])).

fof(f851,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(superposition,[],[f819,f393])).

fof(f393,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f389,f347])).

fof(f347,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f341,f95])).

fof(f95,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f341,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(superposition,[],[f105,f230])).

fof(f230,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(superposition,[],[f222,f95])).

fof(f389,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(superposition,[],[f222,f235])).

fof(f235,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f215,f230])).

fof(f215,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(superposition,[],[f169,f95])).

fof(f819,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(sK1,X0)))) ),
    inference(superposition,[],[f767,f414])).

fof(f98,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f51,f94,f90])).

fof(f51,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f52,f94,f90])).

fof(f52,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:38:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (22577)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.48  % (22593)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.48  % (22585)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (22583)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (22601)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.50  % (22578)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (22580)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (22584)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (22579)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (22598)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (22590)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (22576)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (22587)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (22581)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (22596)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (22582)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (22597)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (22603)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (22575)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (22602)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (22600)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (22599)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (22604)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (22595)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (22592)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (22594)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (22591)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (22592)Refutation not found, incomplete strategy% (22592)------------------------------
% 0.21/0.54  % (22592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22592)Memory used [KB]: 10618
% 0.21/0.54  % (22592)Time elapsed: 0.150 s
% 0.21/0.54  % (22592)------------------------------
% 0.21/0.54  % (22592)------------------------------
% 0.21/0.54  % (22588)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (22586)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (22597)Refutation not found, incomplete strategy% (22597)------------------------------
% 0.21/0.55  % (22597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22597)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22597)Memory used [KB]: 10746
% 0.21/0.55  % (22597)Time elapsed: 0.161 s
% 0.21/0.55  % (22597)------------------------------
% 0.21/0.55  % (22597)------------------------------
% 0.21/0.55  % (22589)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.78/0.60  % (22583)Refutation found. Thanks to Tanya!
% 1.78/0.60  % SZS status Theorem for theBenchmark
% 1.78/0.60  % SZS output start Proof for theBenchmark
% 1.78/0.60  fof(f1128,plain,(
% 1.78/0.60    $false),
% 1.78/0.60    inference(avatar_sat_refutation,[],[f97,f98,f1108,f1121,f1127])).
% 1.78/0.60  fof(f1127,plain,(
% 1.78/0.60    spl3_2 | ~spl3_25),
% 1.78/0.60    inference(avatar_contradiction_clause,[],[f1126])).
% 1.78/0.60  fof(f1126,plain,(
% 1.78/0.60    $false | (spl3_2 | ~spl3_25)),
% 1.78/0.60    inference(subsumption_resolution,[],[f1122,f96])).
% 1.78/0.60  fof(f96,plain,(
% 1.78/0.60    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl3_2),
% 1.78/0.60    inference(avatar_component_clause,[],[f94])).
% 1.78/0.60  fof(f94,plain,(
% 1.78/0.60    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.78/0.60  fof(f1122,plain,(
% 1.78/0.60    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl3_25),
% 1.78/0.60    inference(backward_demodulation,[],[f110,f1117])).
% 1.78/0.60  fof(f1117,plain,(
% 1.78/0.60    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_25),
% 1.78/0.60    inference(avatar_component_clause,[],[f1116])).
% 1.78/0.60  fof(f1116,plain,(
% 1.78/0.60    spl3_25 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.78/0.60  fof(f110,plain,(
% 1.78/0.60    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.78/0.60    inference(subsumption_resolution,[],[f102,f49])).
% 1.78/0.60  fof(f49,plain,(
% 1.78/0.60    l1_pre_topc(sK0)),
% 1.78/0.60    inference(cnf_transformation,[],[f41])).
% 1.78/0.60  fof(f41,plain,(
% 1.78/0.60    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.78/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 1.78/0.60  fof(f39,plain,(
% 1.78/0.60    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.78/0.60    introduced(choice_axiom,[])).
% 1.78/0.60  fof(f40,plain,(
% 1.78/0.60    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.78/0.60    introduced(choice_axiom,[])).
% 1.92/0.61  fof(f38,plain,(
% 1.92/0.61    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.92/0.61    inference(flattening,[],[f37])).
% 1.92/0.61  fof(f37,plain,(
% 1.92/0.61    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.92/0.61    inference(nnf_transformation,[],[f24])).
% 1.92/0.61  fof(f24,plain,(
% 1.92/0.61    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.92/0.61    inference(flattening,[],[f23])).
% 1.92/0.61  fof(f23,plain,(
% 1.92/0.61    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.92/0.61    inference(ennf_transformation,[],[f22])).
% 1.92/0.61  fof(f22,negated_conjecture,(
% 1.92/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.92/0.61    inference(negated_conjecture,[],[f21])).
% 1.92/0.61  fof(f21,conjecture,(
% 1.92/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 1.92/0.61  fof(f102,plain,(
% 1.92/0.61    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.92/0.61    inference(resolution,[],[f50,f57])).
% 1.92/0.61  fof(f57,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f26])).
% 1.92/0.61  fof(f26,plain,(
% 1.92/0.61    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.92/0.61    inference(ennf_transformation,[],[f19])).
% 1.92/0.61  fof(f19,axiom,(
% 1.92/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 1.92/0.61  fof(f50,plain,(
% 1.92/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.92/0.61    inference(cnf_transformation,[],[f41])).
% 1.92/0.61  fof(f1121,plain,(
% 1.92/0.61    spl3_25 | ~spl3_1),
% 1.92/0.61    inference(avatar_split_clause,[],[f1120,f90,f1116])).
% 1.92/0.61  fof(f90,plain,(
% 1.92/0.61    spl3_1 <=> v4_pre_topc(sK1,sK0)),
% 1.92/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.92/0.61  fof(f1120,plain,(
% 1.92/0.61    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.92/0.61    inference(subsumption_resolution,[],[f100,f49])).
% 1.92/0.61  fof(f100,plain,(
% 1.92/0.61    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.92/0.61    inference(resolution,[],[f50,f58])).
% 1.92/0.61  fof(f58,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f28])).
% 1.92/0.61  fof(f28,plain,(
% 1.92/0.61    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.92/0.61    inference(flattening,[],[f27])).
% 1.92/0.61  fof(f27,plain,(
% 1.92/0.61    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.92/0.61    inference(ennf_transformation,[],[f17])).
% 1.92/0.61  fof(f17,axiom,(
% 1.92/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.92/0.61  fof(f1108,plain,(
% 1.92/0.61    spl3_1 | ~spl3_2),
% 1.92/0.61    inference(avatar_contradiction_clause,[],[f1107])).
% 1.92/0.61  fof(f1107,plain,(
% 1.92/0.61    $false | (spl3_1 | ~spl3_2)),
% 1.92/0.61    inference(subsumption_resolution,[],[f1106,f109])).
% 1.92/0.61  fof(f109,plain,(
% 1.92/0.61    sK1 != k2_pre_topc(sK0,sK1) | spl3_1),
% 1.92/0.61    inference(subsumption_resolution,[],[f108,f49])).
% 1.92/0.61  fof(f108,plain,(
% 1.92/0.61    sK1 != k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | spl3_1),
% 1.92/0.61    inference(subsumption_resolution,[],[f107,f92])).
% 1.92/0.61  fof(f92,plain,(
% 1.92/0.61    ~v4_pre_topc(sK1,sK0) | spl3_1),
% 1.92/0.61    inference(avatar_component_clause,[],[f90])).
% 1.92/0.61  fof(f107,plain,(
% 1.92/0.61    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.92/0.61    inference(subsumption_resolution,[],[f101,f48])).
% 1.92/0.61  fof(f48,plain,(
% 1.92/0.61    v2_pre_topc(sK0)),
% 1.92/0.61    inference(cnf_transformation,[],[f41])).
% 1.92/0.61  fof(f101,plain,(
% 1.92/0.61    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.92/0.61    inference(resolution,[],[f50,f59])).
% 1.92/0.61  fof(f59,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f28])).
% 1.92/0.61  fof(f1106,plain,(
% 1.92/0.61    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_2),
% 1.92/0.61    inference(forward_demodulation,[],[f1102,f934])).
% 1.92/0.61  fof(f934,plain,(
% 1.92/0.61    sK1 = k5_xboole_0(sK1,k1_xboole_0)),
% 1.92/0.61    inference(backward_demodulation,[],[f245,f907])).
% 1.92/0.61  fof(f907,plain,(
% 1.92/0.61    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.92/0.61    inference(resolution,[],[f897,f53])).
% 1.92/0.61  fof(f53,plain,(
% 1.92/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f6])).
% 1.92/0.61  fof(f6,axiom,(
% 1.92/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.92/0.61  fof(f897,plain,(
% 1.92/0.61    ( ! [X0] : (~r1_tarski(X0,k5_xboole_0(sK1,sK1)) | k5_xboole_0(sK1,sK1) = X0) )),
% 1.92/0.61    inference(resolution,[],[f893,f70])).
% 1.92/0.61  fof(f70,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f43])).
% 1.92/0.61  fof(f43,plain,(
% 1.92/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.92/0.61    inference(flattening,[],[f42])).
% 1.92/0.61  fof(f42,plain,(
% 1.92/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.92/0.61    inference(nnf_transformation,[],[f2])).
% 1.92/0.61  fof(f2,axiom,(
% 1.92/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.92/0.61  fof(f893,plain,(
% 1.92/0.61    ( ! [X0] : (r1_tarski(k5_xboole_0(sK1,sK1),X0)) )),
% 1.92/0.61    inference(subsumption_resolution,[],[f890,f53])).
% 1.92/0.61  fof(f890,plain,(
% 1.92/0.61    ( ! [X0] : (r1_tarski(k5_xboole_0(sK1,sK1),X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.92/0.61    inference(superposition,[],[f84,f243])).
% 1.92/0.61  fof(f243,plain,(
% 1.92/0.61    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))))),
% 1.92/0.61    inference(superposition,[],[f82,f236])).
% 1.92/0.61  fof(f236,plain,(
% 1.92/0.61    k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) = k5_xboole_0(sK1,sK1)),
% 1.92/0.61    inference(forward_demodulation,[],[f231,f60])).
% 1.92/0.61  fof(f60,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f11])).
% 1.92/0.61  fof(f11,axiom,(
% 1.92/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.92/0.61  fof(f231,plain,(
% 1.92/0.61    k1_setfam_1(k2_tarski(sK1,k1_xboole_0)) = k5_xboole_0(sK1,sK1)),
% 1.92/0.61    inference(superposition,[],[f222,f160])).
% 1.92/0.61  fof(f160,plain,(
% 1.92/0.61    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)),
% 1.92/0.61    inference(superposition,[],[f105,f80])).
% 1.92/0.61  fof(f80,plain,(
% 1.92/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 1.92/0.61    inference(definition_unfolding,[],[f55,f78])).
% 1.92/0.61  fof(f78,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.92/0.61    inference(definition_unfolding,[],[f65,f61])).
% 1.92/0.61  fof(f61,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f15])).
% 1.92/0.61  fof(f15,axiom,(
% 1.92/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.92/0.61  fof(f65,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f3])).
% 1.92/0.61  fof(f3,axiom,(
% 1.92/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.92/0.61  fof(f55,plain,(
% 1.92/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.92/0.61    inference(cnf_transformation,[],[f7])).
% 1.92/0.61  fof(f7,axiom,(
% 1.92/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.92/0.61  fof(f105,plain,(
% 1.92/0.61    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,X1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1)))) )),
% 1.92/0.61    inference(resolution,[],[f50,f85])).
% 1.92/0.61  fof(f85,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 1.92/0.61    inference(definition_unfolding,[],[f76,f78])).
% 1.92/0.61  fof(f76,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f34])).
% 1.92/0.61  fof(f34,plain,(
% 1.92/0.61    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.92/0.61    inference(ennf_transformation,[],[f14])).
% 1.92/0.61  fof(f14,axiom,(
% 1.92/0.61    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.92/0.61  fof(f222,plain,(
% 1.92/0.61    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))) )),
% 1.92/0.61    inference(backward_demodulation,[],[f164,f221])).
% 1.92/0.61  fof(f221,plain,(
% 1.92/0.61    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) )),
% 1.92/0.61    inference(forward_demodulation,[],[f217,f170])).
% 1.92/0.61  fof(f170,plain,(
% 1.92/0.61    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2))) = k7_subset_1(u1_struct_0(sK0),sK1,X2)) )),
% 1.92/0.61    inference(forward_demodulation,[],[f162,f105])).
% 1.92/0.61  fof(f162,plain,(
% 1.92/0.61    ( ! [X2] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X2))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2)))) )),
% 1.92/0.61    inference(superposition,[],[f105,f83])).
% 1.92/0.61  fof(f83,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))))) )),
% 1.92/0.61    inference(definition_unfolding,[],[f66,f78,f78,f61])).
% 1.92/0.61  fof(f66,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f8])).
% 1.92/0.61  fof(f8,axiom,(
% 1.92/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.92/0.61  fof(f217,plain,(
% 1.92/0.61    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) )),
% 1.92/0.61    inference(superposition,[],[f169,f169])).
% 1.92/0.61  fof(f169,plain,(
% 1.92/0.61    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))) )),
% 1.92/0.61    inference(forward_demodulation,[],[f161,f105])).
% 1.92/0.61  fof(f161,plain,(
% 1.92/0.61    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1))))) )),
% 1.92/0.61    inference(superposition,[],[f105,f82])).
% 1.92/0.61  fof(f164,plain,(
% 1.92/0.61    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))))) )),
% 1.92/0.61    inference(superposition,[],[f82,f105])).
% 1.92/0.61  fof(f82,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 1.92/0.61    inference(definition_unfolding,[],[f64,f61,f78,f78])).
% 1.92/0.61  fof(f64,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f9])).
% 1.92/0.61  fof(f9,axiom,(
% 1.92/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.92/0.61  fof(f84,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))),X1) | ~r1_tarski(X0,X1)) )),
% 1.92/0.61    inference(definition_unfolding,[],[f75,f78])).
% 1.92/0.61  fof(f75,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f33])).
% 1.92/0.61  fof(f33,plain,(
% 1.92/0.61    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.92/0.61    inference(ennf_transformation,[],[f4])).
% 1.92/0.61  fof(f4,axiom,(
% 1.92/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 1.92/0.61  fof(f245,plain,(
% 1.92/0.61    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 1.92/0.61    inference(forward_demodulation,[],[f240,f160])).
% 1.92/0.61  fof(f240,plain,(
% 1.92/0.61    k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 1.92/0.61    inference(superposition,[],[f158,f236])).
% 1.92/0.61  fof(f158,plain,(
% 1.92/0.61    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1)))) )),
% 1.92/0.61    inference(superposition,[],[f105,f60])).
% 1.92/0.61  fof(f1102,plain,(
% 1.92/0.61    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0) | ~spl3_2),
% 1.92/0.61    inference(backward_demodulation,[],[f867,f1093])).
% 1.92/0.61  fof(f1093,plain,(
% 1.92/0.61    ( ! [X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1))) )),
% 1.92/0.61    inference(superposition,[],[f1055,f82])).
% 1.92/0.61  fof(f1055,plain,(
% 1.92/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) )),
% 1.92/0.61    inference(resolution,[],[f959,f88])).
% 1.92/0.61  fof(f88,plain,(
% 1.92/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.92/0.61    inference(equality_resolution,[],[f68])).
% 1.92/0.61  fof(f68,plain,(
% 1.92/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.92/0.61    inference(cnf_transformation,[],[f43])).
% 1.92/0.61  fof(f959,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.92/0.61    inference(forward_demodulation,[],[f958,f907])).
% 1.92/0.61  fof(f958,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_tarski(X0,k5_xboole_0(sK1,sK1))) )),
% 1.92/0.61    inference(forward_demodulation,[],[f909,f907])).
% 1.92/0.61  fof(f909,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k5_xboole_0(sK1,sK1) | ~r1_tarski(X0,k5_xboole_0(sK1,sK1))) )),
% 1.92/0.61    inference(resolution,[],[f897,f84])).
% 1.92/0.61  fof(f867,plain,(
% 1.92/0.61    k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_xboole_0,k2_tops_1(sK0,sK1)))) | ~spl3_2),
% 1.92/0.61    inference(forward_demodulation,[],[f866,f335])).
% 1.92/0.61  fof(f335,plain,(
% 1.92/0.61    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.92/0.61    inference(forward_demodulation,[],[f331,f111])).
% 1.92/0.61  fof(f111,plain,(
% 1.92/0.61    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.92/0.61    inference(subsumption_resolution,[],[f103,f49])).
% 1.92/0.61  fof(f103,plain,(
% 1.92/0.61    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.92/0.61    inference(resolution,[],[f50,f56])).
% 1.92/0.61  fof(f56,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f25])).
% 1.92/0.61  fof(f25,plain,(
% 1.92/0.61    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.92/0.61    inference(ennf_transformation,[],[f20])).
% 1.92/0.61  fof(f20,axiom,(
% 1.92/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 1.92/0.61  fof(f331,plain,(
% 1.92/0.61    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.92/0.61    inference(resolution,[],[f117,f50])).
% 1.92/0.61  fof(f117,plain,(
% 1.92/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1)))) )),
% 1.92/0.61    inference(resolution,[],[f106,f86])).
% 1.92/0.61  fof(f86,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.92/0.61    inference(definition_unfolding,[],[f77,f62])).
% 1.92/0.61  fof(f62,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f12])).
% 1.92/0.61  fof(f12,axiom,(
% 1.92/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.92/0.61  fof(f77,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f36])).
% 1.92/0.61  fof(f36,plain,(
% 1.92/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.92/0.61    inference(flattening,[],[f35])).
% 1.92/0.61  fof(f35,plain,(
% 1.92/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.92/0.61    inference(ennf_transformation,[],[f13])).
% 1.92/0.61  fof(f13,axiom,(
% 1.92/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.92/0.61  fof(f106,plain,(
% 1.92/0.61    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.92/0.61    inference(subsumption_resolution,[],[f99,f49])).
% 1.92/0.61  fof(f99,plain,(
% 1.92/0.61    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.92/0.61    inference(resolution,[],[f50,f67])).
% 1.92/0.61  fof(f67,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f30])).
% 1.92/0.61  fof(f30,plain,(
% 1.92/0.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.92/0.61    inference(flattening,[],[f29])).
% 1.92/0.61  fof(f29,plain,(
% 1.92/0.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.92/0.61    inference(ennf_transformation,[],[f18])).
% 1.92/0.61  fof(f18,axiom,(
% 1.92/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.92/0.61  fof(f866,plain,(
% 1.92/0.61    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_xboole_0,k2_tops_1(sK0,sK1)))) | ~spl3_2),
% 1.92/0.61    inference(forward_demodulation,[],[f865,f823])).
% 1.92/0.61  fof(f823,plain,(
% 1.92/0.61    ( ! [X1] : (k3_tarski(k2_tarski(sK1,X1)) = k3_tarski(k2_tarski(X1,sK1))) )),
% 1.92/0.61    inference(superposition,[],[f767,f81])).
% 1.92/0.61  fof(f81,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 1.92/0.61    inference(definition_unfolding,[],[f63,f62,f78])).
% 1.92/0.61  fof(f63,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f10])).
% 1.92/0.61  fof(f10,axiom,(
% 1.92/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.92/0.61  fof(f767,plain,(
% 1.92/0.61    ( ! [X0] : (k3_tarski(k2_tarski(X0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))))) )),
% 1.92/0.61    inference(superposition,[],[f444,f60])).
% 1.92/0.61  fof(f444,plain,(
% 1.92/0.61    ( ! [X8] : (k3_tarski(k2_tarski(sK1,X8)) = k5_xboole_0(sK1,k5_xboole_0(X8,k1_setfam_1(k2_tarski(sK1,X8))))) )),
% 1.92/0.61    inference(superposition,[],[f81,f414])).
% 1.92/0.61  fof(f414,plain,(
% 1.92/0.61    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k1_setfam_1(k2_tarski(X1,sK1))) )),
% 1.92/0.61    inference(superposition,[],[f386,f222])).
% 1.92/0.61  fof(f386,plain,(
% 1.92/0.61    ( ! [X8] : (k1_setfam_1(k2_tarski(X8,sK1)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X8))) )),
% 1.92/0.61    inference(forward_demodulation,[],[f385,f221])).
% 1.92/0.61  fof(f385,plain,(
% 1.92/0.61    ( ! [X8] : (k1_setfam_1(k2_tarski(X8,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X8))))) )),
% 1.92/0.61    inference(forward_demodulation,[],[f379,f158])).
% 1.92/0.61  fof(f379,plain,(
% 1.92/0.61    ( ! [X8] : (k1_setfam_1(k2_tarski(X8,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X8,sK1))))))) )),
% 1.92/0.61    inference(superposition,[],[f82,f354])).
% 1.92/0.61  fof(f354,plain,(
% 1.92/0.61    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,sK1)) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(X0,sK1))))) )),
% 1.92/0.61    inference(superposition,[],[f254,f60])).
% 1.92/0.61  fof(f254,plain,(
% 1.92/0.61    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,X0))))) )),
% 1.92/0.61    inference(forward_demodulation,[],[f250,f222])).
% 1.92/0.61  fof(f250,plain,(
% 1.92/0.61    ( ! [X0] : (k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(sK1,X0))))) )),
% 1.92/0.61    inference(superposition,[],[f222,f170])).
% 1.92/0.61  fof(f865,plain,(
% 1.92/0.61    k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_xboole_0,k2_tops_1(sK0,sK1)))) | ~spl3_2),
% 1.92/0.61    inference(forward_demodulation,[],[f851,f812])).
% 1.92/0.61  fof(f812,plain,(
% 1.92/0.61    k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(k1_xboole_0,k2_tops_1(sK0,sK1)))),
% 1.92/0.61    inference(forward_demodulation,[],[f808,f60])).
% 1.92/0.61  fof(f808,plain,(
% 1.92/0.61    k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k1_xboole_0)) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.92/0.61    inference(superposition,[],[f790,f307])).
% 1.92/0.61  fof(f307,plain,(
% 1.92/0.61    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_xboole_0)),
% 1.92/0.61    inference(superposition,[],[f118,f80])).
% 1.92/0.61  fof(f118,plain,(
% 1.92/0.61    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X1) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1)))) )),
% 1.92/0.61    inference(resolution,[],[f106,f85])).
% 1.92/0.61  fof(f790,plain,(
% 1.92/0.61    ( ! [X2] : (k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2)) = k5_xboole_0(k2_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X2))) )),
% 1.92/0.61    inference(backward_demodulation,[],[f311,f789])).
% 1.92/0.61  fof(f789,plain,(
% 1.92/0.61    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)))) )),
% 1.92/0.61    inference(forward_demodulation,[],[f785,f317])).
% 1.92/0.61  fof(f317,plain,(
% 1.92/0.61    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X2)) )),
% 1.92/0.61    inference(forward_demodulation,[],[f309,f118])).
% 1.92/0.61  fof(f309,plain,(
% 1.92/0.61    ( ! [X2] : (k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2)))) )),
% 1.92/0.61    inference(superposition,[],[f118,f83])).
% 1.92/0.61  fof(f785,plain,(
% 1.92/0.61    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0))) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)))) )),
% 1.92/0.61    inference(superposition,[],[f316,f316])).
% 1.92/0.61  fof(f316,plain,(
% 1.92/0.61    ( ! [X1] : (k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X1))) )),
% 1.92/0.61    inference(forward_demodulation,[],[f308,f118])).
% 1.92/0.61  fof(f308,plain,(
% 1.92/0.61    ( ! [X1] : (k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1))))) )),
% 1.92/0.61    inference(superposition,[],[f118,f82])).
% 1.92/0.61  fof(f311,plain,(
% 1.92/0.61    ( ! [X2] : (k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2)) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X2))))) )),
% 1.92/0.61    inference(superposition,[],[f82,f118])).
% 1.92/0.61  fof(f851,plain,(
% 1.92/0.61    k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl3_2),
% 1.92/0.61    inference(superposition,[],[f819,f393])).
% 1.92/0.61  fof(f393,plain,(
% 1.92/0.61    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_2),
% 1.92/0.61    inference(forward_demodulation,[],[f389,f347])).
% 1.92/0.61  fof(f347,plain,(
% 1.92/0.61    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl3_2),
% 1.92/0.61    inference(forward_demodulation,[],[f341,f95])).
% 1.92/0.61  fof(f95,plain,(
% 1.92/0.61    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl3_2),
% 1.92/0.61    inference(avatar_component_clause,[],[f94])).
% 1.92/0.61  fof(f341,plain,(
% 1.92/0.61    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl3_2),
% 1.92/0.61    inference(superposition,[],[f105,f230])).
% 1.92/0.61  fof(f230,plain,(
% 1.92/0.61    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_2),
% 1.92/0.61    inference(superposition,[],[f222,f95])).
% 1.92/0.61  fof(f389,plain,(
% 1.92/0.61    k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_2),
% 1.92/0.61    inference(superposition,[],[f222,f235])).
% 1.92/0.61  fof(f235,plain,(
% 1.92/0.61    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_2),
% 1.92/0.61    inference(backward_demodulation,[],[f215,f230])).
% 1.92/0.61  fof(f215,plain,(
% 1.92/0.61    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_2),
% 1.92/0.61    inference(superposition,[],[f169,f95])).
% 1.92/0.61  fof(f819,plain,(
% 1.92/0.61    ( ! [X0] : (k3_tarski(k2_tarski(X0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(sK1,X0))))) )),
% 1.92/0.61    inference(superposition,[],[f767,f414])).
% 1.92/0.61  fof(f98,plain,(
% 1.92/0.61    spl3_1 | spl3_2),
% 1.92/0.61    inference(avatar_split_clause,[],[f51,f94,f90])).
% 1.92/0.61  fof(f51,plain,(
% 1.92/0.61    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.92/0.61    inference(cnf_transformation,[],[f41])).
% 1.92/0.61  fof(f97,plain,(
% 1.92/0.61    ~spl3_1 | ~spl3_2),
% 1.92/0.61    inference(avatar_split_clause,[],[f52,f94,f90])).
% 1.92/0.61  fof(f52,plain,(
% 1.92/0.61    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.92/0.61    inference(cnf_transformation,[],[f41])).
% 1.92/0.61  % SZS output end Proof for theBenchmark
% 1.92/0.61  % (22583)------------------------------
% 1.92/0.61  % (22583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.61  % (22583)Termination reason: Refutation
% 1.92/0.61  
% 1.92/0.61  % (22583)Memory used [KB]: 11385
% 1.92/0.61  % (22583)Time elapsed: 0.206 s
% 1.92/0.61  % (22583)------------------------------
% 1.92/0.61  % (22583)------------------------------
% 1.92/0.61  % (22574)Success in time 0.258 s
%------------------------------------------------------------------------------
