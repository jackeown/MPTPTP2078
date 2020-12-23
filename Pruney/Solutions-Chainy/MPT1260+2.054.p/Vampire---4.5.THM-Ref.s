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
% DateTime   : Thu Dec  3 13:11:42 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  177 (1499 expanded)
%              Number of leaves         :   25 ( 461 expanded)
%              Depth                    :   31
%              Number of atoms          :  518 (5512 expanded)
%              Number of equality atoms :  115 (1531 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1711,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f89,f96,f103,f106,f125,f1530,f1537,f1710])).

fof(f1710,plain,
    ( spl4_2
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f1709])).

fof(f1709,plain,
    ( $false
    | spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f1708,f87])).

fof(f87,plain,
    ( k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_2
  <=> k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1708,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f293,f1536])).

fof(f1536,plain,
    ( sK2 = k1_tops_1(sK1,sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f1534])).

fof(f1534,plain,
    ( spl4_9
  <=> sK2 = k1_tops_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f293,plain,(
    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f290,f42])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
      | ~ v3_pre_topc(sK2,sK1) )
    & ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f290,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f48,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1537,plain,
    ( ~ spl4_1
    | spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1532,f101,f1534,f81])).

fof(f81,plain,
    ( spl4_1
  <=> v3_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f101,plain,
    ( spl4_6
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1532,plain,
    ( sK2 = k1_tops_1(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f189,f42])).

fof(f189,plain,
    ( ~ l1_pre_topc(sK1)
    | sK2 = k1_tops_1(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f102,f43])).

fof(f102,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1530,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f1529])).

fof(f1529,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1528,f83])).

fof(f83,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f1528,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1527,f43])).

fof(f1527,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1526,f42])).

fof(f1526,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1501,f41])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f1501,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f1500])).

fof(f1500,plain,
    ( sK2 != sK2
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f95,f1472])).

fof(f1472,plain,
    ( sK2 = k1_tops_1(sK1,sK2)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f1032,f1470])).

fof(f1470,plain,
    ( sK2 = k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tops_1(sK1,sK2)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f1467,f1003])).

fof(f1003,plain,(
    k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = k5_xboole_0(sK2,k1_tops_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f760,f916])).

fof(f916,plain,(
    k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k5_xboole_0(sK2,k1_tops_1(sK1,sK2)) ),
    inference(superposition,[],[f173,f911])).

fof(f911,plain,(
    k1_tops_1(sK1,sK2) = k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) ),
    inference(forward_demodulation,[],[f910,f448])).

fof(f448,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f445,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f445,plain,(
    ! [X2] : k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_xboole_0))) = X2 ),
    inference(resolution,[],[f443,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f53,f52])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f443,plain,(
    ! [X5] : sP0(k1_xboole_0,X5,X5) ),
    inference(forward_demodulation,[],[f440,f392])).

fof(f392,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f389,f116])).

fof(f116,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(resolution,[],[f73,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f55,f52])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f389,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2))) ),
    inference(resolution,[],[f376,f75])).

fof(f376,plain,(
    ! [X23] : sP0(X23,X23,k1_xboole_0) ),
    inference(resolution,[],[f225,f264])).

fof(f264,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f140,f251])).

fof(f251,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f241,f108])).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(superposition,[],[f71,f70])).

fof(f71,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f51,f52,f52])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f241,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(superposition,[],[f72,f108])).

fof(f72,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f54,f52,f69,f69])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f140,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,k5_xboole_0(X11,k1_xboole_0))
      | ~ r2_hidden(X10,k1_xboole_0) ) ),
    inference(resolution,[],[f62,f117])).

fof(f117,plain,(
    ! [X0] : sP0(k1_xboole_0,X0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f79,f70])).

fof(f79,plain,(
    ! [X0,X1] : sP0(X1,X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f67,f69])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X0)
              & r2_hidden(sK3(X0,X1,X2),X1) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f225,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X2,X3] :
      ( sP0(X2,X2,X3)
      | r2_hidden(sK3(X2,X2,X3),X3)
      | r2_hidden(sK3(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(resolution,[],[f65,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f440,plain,(
    ! [X5] : sP0(k5_xboole_0(X5,X5),X5,X5) ),
    inference(superposition,[],[f249,f116])).

fof(f249,plain,(
    ! [X6,X7] : sP0(k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7))),X6,k1_setfam_1(k2_tarski(X6,X7))) ),
    inference(superposition,[],[f79,f72])).

fof(f910,plain,(
    k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) = k5_xboole_0(k1_tops_1(sK1,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f906,f70])).

fof(f906,plain,(
    k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(k1_tops_1(sK1,sK2),k1_xboole_0))) ),
    inference(superposition,[],[f238,f885])).

fof(f885,plain,(
    k1_xboole_0 = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f882,f71])).

fof(f882,plain,(
    k1_xboole_0 = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(k1_tops_1(sK1,sK2),sK2))) ),
    inference(resolution,[],[f880,f75])).

fof(f880,plain,(
    sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f879,f264])).

fof(f879,plain,
    ( sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0)
    | r2_hidden(sK3(sK2,k1_tops_1(sK1,sK2),k1_xboole_0),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f878])).

fof(f878,plain,
    ( sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0)
    | sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0)
    | r2_hidden(sK3(sK2,k1_tops_1(sK1,sK2),k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f732,f65])).

fof(f732,plain,(
    ! [X33] :
      ( r2_hidden(sK3(X33,k1_tops_1(sK1,sK2),k1_xboole_0),sK2)
      | sP0(X33,k1_tops_1(sK1,sK2),k1_xboole_0) ) ),
    inference(resolution,[],[f265,f311])).

fof(f311,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK1,sK2))
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f180,f277])).

fof(f277,plain,(
    k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f274,f42])).

fof(f274,plain,
    ( k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f47,f43])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f180,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k7_subset_1(u1_struct_0(sK1),sK2,X2))
      | r2_hidden(X3,sK2) ) ),
    inference(superposition,[],[f131,f173])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f61,f79])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f265,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,k1_xboole_0),X1)
      | sP0(X0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f264,f64])).

fof(f238,plain,(
    ! [X2,X1] : k1_setfam_1(k2_tarski(X2,X1)) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1)))))) ),
    inference(superposition,[],[f72,f71])).

fof(f173,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK1),sK2,X0) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) ),
    inference(resolution,[],[f74,f43])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f760,plain,(
    k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) ),
    inference(superposition,[],[f255,f277])).

fof(f255,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(sK2,X0)) = k7_subset_1(u1_struct_0(sK1),sK2,k7_subset_1(u1_struct_0(sK1),sK2,X0)) ),
    inference(forward_demodulation,[],[f246,f173])).

fof(f246,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(sK2,X0)) = k7_subset_1(u1_struct_0(sK1),sK2,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0)))) ),
    inference(superposition,[],[f72,f173])).

fof(f1467,plain,
    ( sK2 = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))))
    | ~ spl4_2 ),
    inference(resolution,[],[f1465,f75])).

fof(f1465,plain,
    ( sP0(k2_tops_1(sK1,sK2),sK2,sK2)
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f1464])).

fof(f1464,plain,
    ( sP0(k2_tops_1(sK1,sK2),sK2,sK2)
    | sP0(k2_tops_1(sK1,sK2),sK2,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f1275,f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f64])).

fof(f1275,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK3(k2_tops_1(sK1,sK2),X6,X6),sK2)
        | sP0(k2_tops_1(sK1,sK2),X6,X6) )
    | ~ spl4_2 ),
    inference(resolution,[],[f1268,f350])).

fof(f350,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(X1,X2,X2),X1)
      | sP0(X1,X2,X2) ) ),
    inference(subsumption_resolution,[],[f348,f64])).

fof(f348,plain,(
    ! [X2,X1] :
      ( sP0(X1,X2,X2)
      | r2_hidden(sK3(X1,X2,X2),X1)
      | ~ r2_hidden(sK3(X1,X2,X2),X2) ) ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,(
    ! [X2,X1] :
      ( sP0(X1,X2,X2)
      | r2_hidden(sK3(X1,X2,X2),X1)
      | ~ r2_hidden(sK3(X1,X2,X2),X2)
      | sP0(X1,X2,X2) ) ),
    inference(resolution,[],[f216,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1268,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tops_1(sK1,sK2))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f1242,f62])).

fof(f1242,plain,
    ( sP0(sK2,k2_pre_topc(sK1,sK2),k2_tops_1(sK1,sK2))
    | ~ spl4_2 ),
    inference(superposition,[],[f1212,f86])).

fof(f86,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f1212,plain,(
    ! [X0] : sP0(X0,k2_pre_topc(sK1,sK2),k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0)) ),
    inference(superposition,[],[f79,f757])).

fof(f757,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) ),
    inference(subsumption_resolution,[],[f754,f42])).

fof(f754,plain,(
    ! [X0] :
      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f174,f43])).

fof(f174,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3) = k5_xboole_0(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f74,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f1032,plain,(
    k1_tops_1(sK1,sK2) = k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tops_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f317,f1003])).

fof(f317,plain,(
    k1_tops_1(sK1,sK2) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2)))) ),
    inference(resolution,[],[f313,f75])).

fof(f313,plain,(
    sP0(k2_tops_1(sK1,sK2),sK2,k1_tops_1(sK1,sK2)) ),
    inference(superposition,[],[f181,f277])).

fof(f181,plain,(
    ! [X4] : sP0(X4,sK2,k7_subset_1(u1_struct_0(sK1),sK2,X4)) ),
    inference(superposition,[],[f79,f173])).

fof(f95,plain,
    ( ! [X2,X0] :
        ( k1_tops_1(X0,X2) != X2
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X2,X0) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_4
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X2) != X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f125,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f123,f42])).

fof(f123,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f122,f41])).

fof(f122,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f99,f43])).

fof(f99,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_5
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f106,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f104,f42])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f92,f43])).

fof(f92,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_3
  <=> ! [X1,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f103,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f49,f101,f98])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f96,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f50,f94,f91])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f44,f85,f81])).

fof(f44,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f45,f85,f81])).

fof(f45,plain,
    ( k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (8537)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (8526)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (8546)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (8527)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (8528)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (8523)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (8529)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (8536)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (8545)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (8544)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (8536)Refutation not found, incomplete strategy% (8536)------------------------------
% 0.21/0.52  % (8536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8520)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (8536)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8536)Memory used [KB]: 10618
% 0.21/0.53  % (8536)Time elapsed: 0.113 s
% 0.21/0.53  % (8536)------------------------------
% 0.21/0.53  % (8536)------------------------------
% 0.21/0.53  % (8535)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (8522)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (8548)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (8525)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (8548)Refutation not found, incomplete strategy% (8548)------------------------------
% 0.21/0.53  % (8548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8548)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8548)Memory used [KB]: 10746
% 0.21/0.53  % (8548)Time elapsed: 0.131 s
% 0.21/0.53  % (8548)------------------------------
% 0.21/0.53  % (8548)------------------------------
% 0.21/0.54  % (8534)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (8539)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (8538)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (8533)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (8521)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (8540)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (8547)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (8547)Refutation not found, incomplete strategy% (8547)------------------------------
% 0.21/0.54  % (8547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8547)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8547)Memory used [KB]: 6140
% 0.21/0.54  % (8547)Time elapsed: 0.139 s
% 0.21/0.54  % (8547)------------------------------
% 0.21/0.54  % (8547)------------------------------
% 0.21/0.54  % (8544)Refutation not found, incomplete strategy% (8544)------------------------------
% 0.21/0.54  % (8544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8544)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8544)Memory used [KB]: 10618
% 0.21/0.54  % (8544)Time elapsed: 0.127 s
% 0.21/0.54  % (8544)------------------------------
% 0.21/0.54  % (8544)------------------------------
% 0.21/0.54  % (8532)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (8531)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (8530)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (8543)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (8530)Refutation not found, incomplete strategy% (8530)------------------------------
% 0.21/0.55  % (8530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8542)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (8549)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (8530)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8530)Memory used [KB]: 10746
% 0.21/0.56  % (8530)Time elapsed: 0.149 s
% 0.21/0.56  % (8530)------------------------------
% 0.21/0.56  % (8530)------------------------------
% 0.21/0.56  % (8549)Refutation not found, incomplete strategy% (8549)------------------------------
% 0.21/0.56  % (8549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8549)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8549)Memory used [KB]: 1663
% 0.21/0.56  % (8549)Time elapsed: 0.002 s
% 0.21/0.56  % (8549)------------------------------
% 0.21/0.56  % (8549)------------------------------
% 0.21/0.56  % (8541)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.64/0.57  % (8524)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.81/0.62  % (8526)Refutation found. Thanks to Tanya!
% 1.81/0.62  % SZS status Theorem for theBenchmark
% 1.81/0.62  % SZS output start Proof for theBenchmark
% 1.81/0.62  fof(f1711,plain,(
% 1.81/0.62    $false),
% 1.81/0.62    inference(avatar_sat_refutation,[],[f88,f89,f96,f103,f106,f125,f1530,f1537,f1710])).
% 1.81/0.62  fof(f1710,plain,(
% 1.81/0.62    spl4_2 | ~spl4_9),
% 1.81/0.62    inference(avatar_contradiction_clause,[],[f1709])).
% 1.81/0.62  fof(f1709,plain,(
% 1.81/0.62    $false | (spl4_2 | ~spl4_9)),
% 1.81/0.62    inference(subsumption_resolution,[],[f1708,f87])).
% 1.81/0.62  fof(f87,plain,(
% 1.81/0.62    k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | spl4_2),
% 1.81/0.62    inference(avatar_component_clause,[],[f85])).
% 1.81/0.62  fof(f85,plain,(
% 1.81/0.62    spl4_2 <=> k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.81/0.62  fof(f1708,plain,(
% 1.81/0.62    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~spl4_9),
% 1.81/0.62    inference(forward_demodulation,[],[f293,f1536])).
% 1.81/0.62  fof(f1536,plain,(
% 1.81/0.62    sK2 = k1_tops_1(sK1,sK2) | ~spl4_9),
% 1.81/0.62    inference(avatar_component_clause,[],[f1534])).
% 1.81/0.62  fof(f1534,plain,(
% 1.81/0.62    spl4_9 <=> sK2 = k1_tops_1(sK1,sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.81/0.62  fof(f293,plain,(
% 1.81/0.62    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2))),
% 1.81/0.62    inference(subsumption_resolution,[],[f290,f42])).
% 1.81/0.62  fof(f42,plain,(
% 1.81/0.62    l1_pre_topc(sK1)),
% 1.81/0.62    inference(cnf_transformation,[],[f32])).
% 1.81/0.62  fof(f32,plain,(
% 1.81/0.62    ((k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~v3_pre_topc(sK2,sK1)) & (k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 1.81/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f31,f30])).
% 1.81/0.62  fof(f30,plain,(
% 1.81/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK1,X1) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | ~v3_pre_topc(X1,sK1)) & (k2_tops_1(sK1,X1) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.81/0.62    introduced(choice_axiom,[])).
% 1.81/0.62  fof(f31,plain,(
% 1.81/0.62    ? [X1] : ((k2_tops_1(sK1,X1) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | ~v3_pre_topc(X1,sK1)) & (k2_tops_1(sK1,X1) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) => ((k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~v3_pre_topc(sK2,sK1)) & (k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.81/0.62    introduced(choice_axiom,[])).
% 1.81/0.62  fof(f29,plain,(
% 1.81/0.62    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.81/0.62    inference(flattening,[],[f28])).
% 1.81/0.62  fof(f28,plain,(
% 1.81/0.62    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.81/0.62    inference(nnf_transformation,[],[f17])).
% 1.81/0.62  fof(f17,plain,(
% 1.81/0.62    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.81/0.62    inference(flattening,[],[f16])).
% 1.81/0.62  fof(f16,plain,(
% 1.81/0.62    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.81/0.62    inference(ennf_transformation,[],[f15])).
% 1.81/0.62  fof(f15,negated_conjecture,(
% 1.81/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.81/0.62    inference(negated_conjecture,[],[f14])).
% 1.81/0.62  fof(f14,conjecture,(
% 1.81/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 1.81/0.62  fof(f290,plain,(
% 1.81/0.62    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) | ~l1_pre_topc(sK1)),
% 1.81/0.62    inference(resolution,[],[f48,f43])).
% 1.81/0.62  fof(f43,plain,(
% 1.81/0.62    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.81/0.62    inference(cnf_transformation,[],[f32])).
% 1.81/0.62  fof(f48,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f19])).
% 1.81/0.62  fof(f19,plain,(
% 1.81/0.62    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f11])).
% 1.81/0.62  fof(f11,axiom,(
% 1.81/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.81/0.62  fof(f1537,plain,(
% 1.81/0.62    ~spl4_1 | spl4_9 | ~spl4_6),
% 1.81/0.62    inference(avatar_split_clause,[],[f1532,f101,f1534,f81])).
% 1.81/0.62  fof(f81,plain,(
% 1.81/0.62    spl4_1 <=> v3_pre_topc(sK2,sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.81/0.62  fof(f101,plain,(
% 1.81/0.62    spl4_6 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.81/0.62  fof(f1532,plain,(
% 1.81/0.62    sK2 = k1_tops_1(sK1,sK2) | ~v3_pre_topc(sK2,sK1) | ~spl4_6),
% 1.81/0.62    inference(subsumption_resolution,[],[f189,f42])).
% 1.81/0.62  fof(f189,plain,(
% 1.81/0.62    ~l1_pre_topc(sK1) | sK2 = k1_tops_1(sK1,sK2) | ~v3_pre_topc(sK2,sK1) | ~spl4_6),
% 1.81/0.62    inference(resolution,[],[f102,f43])).
% 1.81/0.62  fof(f102,plain,(
% 1.81/0.62    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl4_6),
% 1.81/0.62    inference(avatar_component_clause,[],[f101])).
% 1.81/0.62  fof(f1530,plain,(
% 1.81/0.62    spl4_1 | ~spl4_2 | ~spl4_4),
% 1.81/0.62    inference(avatar_contradiction_clause,[],[f1529])).
% 1.81/0.62  fof(f1529,plain,(
% 1.81/0.62    $false | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 1.81/0.62    inference(subsumption_resolution,[],[f1528,f83])).
% 1.81/0.62  fof(f83,plain,(
% 1.81/0.62    ~v3_pre_topc(sK2,sK1) | spl4_1),
% 1.81/0.62    inference(avatar_component_clause,[],[f81])).
% 1.81/0.62  fof(f1528,plain,(
% 1.81/0.62    v3_pre_topc(sK2,sK1) | (~spl4_2 | ~spl4_4)),
% 1.81/0.62    inference(subsumption_resolution,[],[f1527,f43])).
% 1.81/0.62  fof(f1527,plain,(
% 1.81/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK2,sK1) | (~spl4_2 | ~spl4_4)),
% 1.81/0.62    inference(subsumption_resolution,[],[f1526,f42])).
% 1.81/0.62  fof(f1526,plain,(
% 1.81/0.62    ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK2,sK1) | (~spl4_2 | ~spl4_4)),
% 1.81/0.62    inference(subsumption_resolution,[],[f1501,f41])).
% 1.81/0.62  fof(f41,plain,(
% 1.81/0.62    v2_pre_topc(sK1)),
% 1.81/0.62    inference(cnf_transformation,[],[f32])).
% 1.81/0.62  fof(f1501,plain,(
% 1.81/0.62    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK2,sK1) | (~spl4_2 | ~spl4_4)),
% 1.81/0.62    inference(trivial_inequality_removal,[],[f1500])).
% 1.81/0.62  fof(f1500,plain,(
% 1.81/0.62    sK2 != sK2 | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK2,sK1) | (~spl4_2 | ~spl4_4)),
% 1.81/0.62    inference(superposition,[],[f95,f1472])).
% 1.81/0.62  fof(f1472,plain,(
% 1.81/0.62    sK2 = k1_tops_1(sK1,sK2) | ~spl4_2),
% 1.81/0.62    inference(backward_demodulation,[],[f1032,f1470])).
% 1.81/0.62  fof(f1470,plain,(
% 1.81/0.62    sK2 = k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tops_1(sK1,sK2))) | ~spl4_2),
% 1.81/0.62    inference(forward_demodulation,[],[f1467,f1003])).
% 1.81/0.62  fof(f1003,plain,(
% 1.81/0.62    k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = k5_xboole_0(sK2,k1_tops_1(sK1,sK2))),
% 1.81/0.62    inference(backward_demodulation,[],[f760,f916])).
% 1.81/0.62  fof(f916,plain,(
% 1.81/0.62    k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k5_xboole_0(sK2,k1_tops_1(sK1,sK2))),
% 1.81/0.62    inference(superposition,[],[f173,f911])).
% 1.81/0.62  fof(f911,plain,(
% 1.81/0.62    k1_tops_1(sK1,sK2) = k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2)))),
% 1.81/0.62    inference(forward_demodulation,[],[f910,f448])).
% 1.81/0.62  fof(f448,plain,(
% 1.81/0.62    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.81/0.62    inference(forward_demodulation,[],[f445,f70])).
% 1.81/0.62  fof(f70,plain,(
% 1.81/0.62    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.81/0.62    inference(definition_unfolding,[],[f46,f52])).
% 1.81/0.62  fof(f52,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f9])).
% 1.81/0.62  fof(f9,axiom,(
% 1.81/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.81/0.62  fof(f46,plain,(
% 1.81/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f6])).
% 1.81/0.62  fof(f6,axiom,(
% 1.81/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.81/0.62  fof(f445,plain,(
% 1.81/0.62    ( ! [X2] : (k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k1_xboole_0))) = X2) )),
% 1.81/0.62    inference(resolution,[],[f443,f75])).
% 1.81/0.62  fof(f75,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2) )),
% 1.81/0.62    inference(definition_unfolding,[],[f68,f69])).
% 1.81/0.62  fof(f69,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.81/0.62    inference(definition_unfolding,[],[f53,f52])).
% 1.81/0.62  fof(f53,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f4])).
% 1.81/0.62  fof(f4,axiom,(
% 1.81/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.81/0.62  fof(f68,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f40])).
% 1.81/0.62  fof(f40,plain,(
% 1.81/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.81/0.62    inference(nnf_transformation,[],[f27])).
% 1.81/0.62  fof(f27,plain,(
% 1.81/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.81/0.62    inference(definition_folding,[],[f2,f26])).
% 1.81/0.62  fof(f26,plain,(
% 1.81/0.62    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.81/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.81/0.62  fof(f2,axiom,(
% 1.81/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.81/0.62  fof(f443,plain,(
% 1.81/0.62    ( ! [X5] : (sP0(k1_xboole_0,X5,X5)) )),
% 1.81/0.62    inference(forward_demodulation,[],[f440,f392])).
% 1.81/0.62  fof(f392,plain,(
% 1.81/0.62    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 1.81/0.62    inference(forward_demodulation,[],[f389,f116])).
% 1.81/0.62  fof(f116,plain,(
% 1.81/0.62    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.81/0.62    inference(resolution,[],[f73,f77])).
% 1.81/0.62  fof(f77,plain,(
% 1.81/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.81/0.62    inference(equality_resolution,[],[f58])).
% 1.81/0.62  fof(f58,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.81/0.62    inference(cnf_transformation,[],[f34])).
% 1.81/0.62  fof(f34,plain,(
% 1.81/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.62    inference(flattening,[],[f33])).
% 1.81/0.62  fof(f33,plain,(
% 1.81/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.62    inference(nnf_transformation,[],[f3])).
% 1.81/0.62  fof(f3,axiom,(
% 1.81/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.81/0.62  fof(f73,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.81/0.62    inference(definition_unfolding,[],[f55,f52])).
% 1.81/0.62  fof(f55,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f22])).
% 1.81/0.62  fof(f22,plain,(
% 1.81/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.81/0.62    inference(ennf_transformation,[],[f5])).
% 1.81/0.62  fof(f5,axiom,(
% 1.81/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.81/0.62  fof(f389,plain,(
% 1.81/0.62    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))) )),
% 1.81/0.62    inference(resolution,[],[f376,f75])).
% 1.81/0.62  fof(f376,plain,(
% 1.81/0.62    ( ! [X23] : (sP0(X23,X23,k1_xboole_0)) )),
% 1.81/0.62    inference(resolution,[],[f225,f264])).
% 1.81/0.62  fof(f264,plain,(
% 1.81/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.81/0.62    inference(duplicate_literal_removal,[],[f258])).
% 1.81/0.62  fof(f258,plain,(
% 1.81/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.81/0.62    inference(superposition,[],[f140,f251])).
% 1.81/0.62  fof(f251,plain,(
% 1.81/0.62    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.81/0.62    inference(forward_demodulation,[],[f241,f108])).
% 1.81/0.62  fof(f108,plain,(
% 1.81/0.62    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 1.81/0.62    inference(superposition,[],[f71,f70])).
% 1.81/0.62  fof(f71,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.81/0.62    inference(definition_unfolding,[],[f51,f52,f52])).
% 1.81/0.62  fof(f51,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f1])).
% 1.81/0.62  fof(f1,axiom,(
% 1.81/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.81/0.62  fof(f241,plain,(
% 1.81/0.62    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))))),
% 1.81/0.62    inference(superposition,[],[f72,f108])).
% 1.81/0.62  fof(f72,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 1.81/0.62    inference(definition_unfolding,[],[f54,f52,f69,f69])).
% 1.81/0.62  fof(f54,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f7])).
% 1.81/0.62  fof(f7,axiom,(
% 1.81/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.81/0.62  fof(f140,plain,(
% 1.81/0.62    ( ! [X10,X11] : (~r2_hidden(X10,k5_xboole_0(X11,k1_xboole_0)) | ~r2_hidden(X10,k1_xboole_0)) )),
% 1.81/0.62    inference(resolution,[],[f62,f117])).
% 1.81/0.62  fof(f117,plain,(
% 1.81/0.62    ( ! [X0] : (sP0(k1_xboole_0,X0,k5_xboole_0(X0,k1_xboole_0))) )),
% 1.81/0.62    inference(superposition,[],[f79,f70])).
% 1.81/0.62  fof(f79,plain,(
% 1.81/0.62    ( ! [X0,X1] : (sP0(X1,X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 1.81/0.62    inference(equality_resolution,[],[f76])).
% 1.81/0.62  fof(f76,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 1.81/0.62    inference(definition_unfolding,[],[f67,f69])).
% 1.81/0.62  fof(f67,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.81/0.62    inference(cnf_transformation,[],[f40])).
% 1.81/0.62  fof(f62,plain,(
% 1.81/0.62    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f39])).
% 1.81/0.62  fof(f39,plain,(
% 1.81/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.81/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 1.81/0.62  fof(f38,plain,(
% 1.81/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.81/0.62    introduced(choice_axiom,[])).
% 1.81/0.63  fof(f37,plain,(
% 1.81/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.81/0.63    inference(rectify,[],[f36])).
% 1.81/0.63  fof(f36,plain,(
% 1.81/0.63    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.81/0.63    inference(flattening,[],[f35])).
% 1.81/0.63  fof(f35,plain,(
% 1.81/0.63    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.81/0.63    inference(nnf_transformation,[],[f26])).
% 1.81/0.63  fof(f225,plain,(
% 1.81/0.63    ( ! [X2,X3] : (r2_hidden(sK3(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 1.81/0.63    inference(duplicate_literal_removal,[],[f224])).
% 1.81/0.63  fof(f224,plain,(
% 1.81/0.63    ( ! [X2,X3] : (sP0(X2,X2,X3) | r2_hidden(sK3(X2,X2,X3),X3) | r2_hidden(sK3(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 1.81/0.63    inference(resolution,[],[f65,f64])).
% 1.81/0.63  fof(f64,plain,(
% 1.81/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f39])).
% 1.81/0.63  fof(f65,plain,(
% 1.81/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | sP0(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f39])).
% 1.81/0.63  fof(f440,plain,(
% 1.81/0.63    ( ! [X5] : (sP0(k5_xboole_0(X5,X5),X5,X5)) )),
% 1.81/0.63    inference(superposition,[],[f249,f116])).
% 1.81/0.63  fof(f249,plain,(
% 1.81/0.63    ( ! [X6,X7] : (sP0(k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7))),X6,k1_setfam_1(k2_tarski(X6,X7)))) )),
% 1.81/0.63    inference(superposition,[],[f79,f72])).
% 1.81/0.63  fof(f910,plain,(
% 1.81/0.63    k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) = k5_xboole_0(k1_tops_1(sK1,sK2),k1_xboole_0)),
% 1.81/0.63    inference(forward_demodulation,[],[f906,f70])).
% 1.81/0.63  fof(f906,plain,(
% 1.81/0.63    k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(k1_tops_1(sK1,sK2),k1_xboole_0)))),
% 1.81/0.63    inference(superposition,[],[f238,f885])).
% 1.81/0.63  fof(f885,plain,(
% 1.81/0.63    k1_xboole_0 = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))))),
% 1.81/0.63    inference(forward_demodulation,[],[f882,f71])).
% 1.81/0.63  fof(f882,plain,(
% 1.81/0.63    k1_xboole_0 = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(k1_tops_1(sK1,sK2),sK2)))),
% 1.81/0.63    inference(resolution,[],[f880,f75])).
% 1.81/0.63  fof(f880,plain,(
% 1.81/0.63    sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0)),
% 1.81/0.63    inference(subsumption_resolution,[],[f879,f264])).
% 1.81/0.63  fof(f879,plain,(
% 1.81/0.63    sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0) | r2_hidden(sK3(sK2,k1_tops_1(sK1,sK2),k1_xboole_0),k1_xboole_0)),
% 1.81/0.63    inference(duplicate_literal_removal,[],[f878])).
% 1.81/0.63  fof(f878,plain,(
% 1.81/0.63    sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0) | sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0) | r2_hidden(sK3(sK2,k1_tops_1(sK1,sK2),k1_xboole_0),k1_xboole_0)),
% 1.81/0.63    inference(resolution,[],[f732,f65])).
% 1.81/0.63  fof(f732,plain,(
% 1.81/0.63    ( ! [X33] : (r2_hidden(sK3(X33,k1_tops_1(sK1,sK2),k1_xboole_0),sK2) | sP0(X33,k1_tops_1(sK1,sK2),k1_xboole_0)) )),
% 1.81/0.63    inference(resolution,[],[f265,f311])).
% 1.81/0.63  fof(f311,plain,(
% 1.81/0.63    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK1,sK2)) | r2_hidden(X0,sK2)) )),
% 1.81/0.63    inference(superposition,[],[f180,f277])).
% 1.81/0.63  fof(f277,plain,(
% 1.81/0.63    k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2))),
% 1.81/0.63    inference(subsumption_resolution,[],[f274,f42])).
% 1.81/0.63  fof(f274,plain,(
% 1.81/0.63    k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) | ~l1_pre_topc(sK1)),
% 1.81/0.63    inference(resolution,[],[f47,f43])).
% 1.81/0.63  fof(f47,plain,(
% 1.81/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f18])).
% 1.81/0.63  fof(f18,plain,(
% 1.81/0.63    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.81/0.63    inference(ennf_transformation,[],[f13])).
% 1.81/0.63  fof(f13,axiom,(
% 1.81/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.81/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 1.81/0.63  fof(f180,plain,(
% 1.81/0.63    ( ! [X2,X3] : (~r2_hidden(X3,k7_subset_1(u1_struct_0(sK1),sK2,X2)) | r2_hidden(X3,sK2)) )),
% 1.81/0.63    inference(superposition,[],[f131,f173])).
% 1.81/0.63  fof(f131,plain,(
% 1.81/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) | r2_hidden(X0,X1)) )),
% 1.81/0.63    inference(resolution,[],[f61,f79])).
% 1.81/0.63  fof(f61,plain,(
% 1.81/0.63    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f39])).
% 1.81/0.63  fof(f265,plain,(
% 1.81/0.63    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,k1_xboole_0),X1) | sP0(X0,X1,k1_xboole_0)) )),
% 1.81/0.63    inference(resolution,[],[f264,f64])).
% 1.81/0.63  fof(f238,plain,(
% 1.81/0.63    ( ! [X2,X1] : (k1_setfam_1(k2_tarski(X2,X1)) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X2,X1))))))) )),
% 1.81/0.63    inference(superposition,[],[f72,f71])).
% 1.81/0.63  fof(f173,plain,(
% 1.81/0.63    ( ! [X0] : (k7_subset_1(u1_struct_0(sK1),sK2,X0) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0)))) )),
% 1.81/0.63    inference(resolution,[],[f74,f43])).
% 1.81/0.63  fof(f74,plain,(
% 1.81/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 1.81/0.63    inference(definition_unfolding,[],[f60,f69])).
% 1.81/0.63  fof(f60,plain,(
% 1.81/0.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.81/0.63    inference(cnf_transformation,[],[f25])).
% 1.81/0.63  fof(f25,plain,(
% 1.81/0.63    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.81/0.63    inference(ennf_transformation,[],[f8])).
% 1.81/0.63  fof(f8,axiom,(
% 1.81/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.81/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.81/0.63  fof(f760,plain,(
% 1.81/0.63    k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2))),
% 1.81/0.63    inference(superposition,[],[f255,f277])).
% 1.81/0.63  fof(f255,plain,(
% 1.81/0.63    ( ! [X0] : (k1_setfam_1(k2_tarski(sK2,X0)) = k7_subset_1(u1_struct_0(sK1),sK2,k7_subset_1(u1_struct_0(sK1),sK2,X0))) )),
% 1.81/0.63    inference(forward_demodulation,[],[f246,f173])).
% 1.81/0.63  fof(f246,plain,(
% 1.81/0.63    ( ! [X0] : (k1_setfam_1(k2_tarski(sK2,X0)) = k7_subset_1(u1_struct_0(sK1),sK2,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))))) )),
% 1.81/0.63    inference(superposition,[],[f72,f173])).
% 1.81/0.63  fof(f1467,plain,(
% 1.81/0.63    sK2 = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2)))) | ~spl4_2),
% 1.81/0.63    inference(resolution,[],[f1465,f75])).
% 1.81/0.63  fof(f1465,plain,(
% 1.81/0.63    sP0(k2_tops_1(sK1,sK2),sK2,sK2) | ~spl4_2),
% 1.81/0.63    inference(duplicate_literal_removal,[],[f1464])).
% 1.81/0.63  fof(f1464,plain,(
% 1.81/0.63    sP0(k2_tops_1(sK1,sK2),sK2,sK2) | sP0(k2_tops_1(sK1,sK2),sK2,sK2) | ~spl4_2),
% 1.81/0.63    inference(resolution,[],[f1275,f216])).
% 1.81/0.63  fof(f216,plain,(
% 1.81/0.63    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 1.81/0.63    inference(factoring,[],[f64])).
% 1.81/0.63  fof(f1275,plain,(
% 1.81/0.63    ( ! [X6] : (~r2_hidden(sK3(k2_tops_1(sK1,sK2),X6,X6),sK2) | sP0(k2_tops_1(sK1,sK2),X6,X6)) ) | ~spl4_2),
% 1.81/0.63    inference(resolution,[],[f1268,f350])).
% 1.81/0.63  fof(f350,plain,(
% 1.81/0.63    ( ! [X2,X1] : (r2_hidden(sK3(X1,X2,X2),X1) | sP0(X1,X2,X2)) )),
% 1.81/0.63    inference(subsumption_resolution,[],[f348,f64])).
% 1.81/0.63  fof(f348,plain,(
% 1.81/0.63    ( ! [X2,X1] : (sP0(X1,X2,X2) | r2_hidden(sK3(X1,X2,X2),X1) | ~r2_hidden(sK3(X1,X2,X2),X2)) )),
% 1.81/0.63    inference(duplicate_literal_removal,[],[f332])).
% 1.81/0.63  fof(f332,plain,(
% 1.81/0.63    ( ! [X2,X1] : (sP0(X1,X2,X2) | r2_hidden(sK3(X1,X2,X2),X1) | ~r2_hidden(sK3(X1,X2,X2),X2) | sP0(X1,X2,X2)) )),
% 1.81/0.63    inference(resolution,[],[f216,f66])).
% 1.81/0.63  fof(f66,plain,(
% 1.81/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f39])).
% 1.81/0.63  fof(f1268,plain,(
% 1.81/0.63    ( ! [X1] : (~r2_hidden(X1,k2_tops_1(sK1,sK2)) | ~r2_hidden(X1,sK2)) ) | ~spl4_2),
% 1.81/0.63    inference(resolution,[],[f1242,f62])).
% 1.81/0.63  fof(f1242,plain,(
% 1.81/0.63    sP0(sK2,k2_pre_topc(sK1,sK2),k2_tops_1(sK1,sK2)) | ~spl4_2),
% 1.81/0.63    inference(superposition,[],[f1212,f86])).
% 1.81/0.63  fof(f86,plain,(
% 1.81/0.63    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~spl4_2),
% 1.81/0.63    inference(avatar_component_clause,[],[f85])).
% 1.81/0.63  fof(f1212,plain,(
% 1.81/0.63    ( ! [X0] : (sP0(X0,k2_pre_topc(sK1,sK2),k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0))) )),
% 1.81/0.63    inference(superposition,[],[f79,f757])).
% 1.81/0.63  fof(f757,plain,(
% 1.81/0.63    ( ! [X0] : (k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0)))) )),
% 1.81/0.63    inference(subsumption_resolution,[],[f754,f42])).
% 1.81/0.63  fof(f754,plain,(
% 1.81/0.63    ( ! [X0] : (k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) | ~l1_pre_topc(sK1)) )),
% 1.81/0.63    inference(resolution,[],[f174,f43])).
% 1.81/0.63  fof(f174,plain,(
% 1.81/0.63    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3) = k5_xboole_0(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3))) | ~l1_pre_topc(X1)) )),
% 1.81/0.63    inference(resolution,[],[f74,f56])).
% 1.81/0.63  fof(f56,plain,(
% 1.81/0.63    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f24])).
% 1.81/0.63  fof(f24,plain,(
% 1.81/0.63    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.81/0.63    inference(flattening,[],[f23])).
% 1.81/0.63  fof(f23,plain,(
% 1.81/0.63    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.81/0.63    inference(ennf_transformation,[],[f10])).
% 1.81/0.63  fof(f10,axiom,(
% 1.81/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.81/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.81/0.63  fof(f1032,plain,(
% 1.81/0.63    k1_tops_1(sK1,sK2) = k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tops_1(sK1,sK2)))),
% 1.81/0.63    inference(backward_demodulation,[],[f317,f1003])).
% 1.81/0.63  fof(f317,plain,(
% 1.81/0.63    k1_tops_1(sK1,sK2) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))))),
% 1.81/0.63    inference(resolution,[],[f313,f75])).
% 1.81/0.63  fof(f313,plain,(
% 1.81/0.63    sP0(k2_tops_1(sK1,sK2),sK2,k1_tops_1(sK1,sK2))),
% 1.81/0.63    inference(superposition,[],[f181,f277])).
% 1.81/0.63  fof(f181,plain,(
% 1.81/0.63    ( ! [X4] : (sP0(X4,sK2,k7_subset_1(u1_struct_0(sK1),sK2,X4))) )),
% 1.81/0.63    inference(superposition,[],[f79,f173])).
% 1.81/0.63  fof(f95,plain,(
% 1.81/0.63    ( ! [X2,X0] : (k1_tops_1(X0,X2) != X2 | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0)) ) | ~spl4_4),
% 1.81/0.63    inference(avatar_component_clause,[],[f94])).
% 1.81/0.63  fof(f94,plain,(
% 1.81/0.63    spl4_4 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2)),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.81/0.63  fof(f125,plain,(
% 1.81/0.63    ~spl4_5),
% 1.81/0.63    inference(avatar_contradiction_clause,[],[f124])).
% 1.81/0.63  fof(f124,plain,(
% 1.81/0.63    $false | ~spl4_5),
% 1.81/0.63    inference(subsumption_resolution,[],[f123,f42])).
% 1.81/0.63  fof(f123,plain,(
% 1.81/0.63    ~l1_pre_topc(sK1) | ~spl4_5),
% 1.81/0.63    inference(subsumption_resolution,[],[f122,f41])).
% 1.81/0.63  fof(f122,plain,(
% 1.81/0.63    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~spl4_5),
% 1.81/0.63    inference(resolution,[],[f99,f43])).
% 1.81/0.63  fof(f99,plain,(
% 1.81/0.63    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl4_5),
% 1.81/0.63    inference(avatar_component_clause,[],[f98])).
% 1.81/0.63  fof(f98,plain,(
% 1.81/0.63    spl4_5 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.81/0.63  fof(f106,plain,(
% 1.81/0.63    ~spl4_3),
% 1.81/0.63    inference(avatar_contradiction_clause,[],[f105])).
% 1.81/0.63  fof(f105,plain,(
% 1.81/0.63    $false | ~spl4_3),
% 1.81/0.63    inference(subsumption_resolution,[],[f104,f42])).
% 1.81/0.63  fof(f104,plain,(
% 1.81/0.63    ~l1_pre_topc(sK1) | ~spl4_3),
% 1.81/0.63    inference(resolution,[],[f92,f43])).
% 1.81/0.63  fof(f92,plain,(
% 1.81/0.63    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl4_3),
% 1.81/0.63    inference(avatar_component_clause,[],[f91])).
% 1.81/0.63  fof(f91,plain,(
% 1.81/0.63    spl4_3 <=> ! [X1,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 1.81/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.81/0.63  fof(f103,plain,(
% 1.81/0.63    spl4_5 | spl4_6),
% 1.81/0.63    inference(avatar_split_clause,[],[f49,f101,f98])).
% 1.81/0.63  fof(f49,plain,(
% 1.81/0.63    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f21])).
% 1.81/0.63  fof(f21,plain,(
% 1.81/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.81/0.63    inference(flattening,[],[f20])).
% 1.81/0.63  fof(f20,plain,(
% 1.81/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.81/0.63    inference(ennf_transformation,[],[f12])).
% 1.81/0.63  fof(f12,axiom,(
% 1.81/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.81/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 1.81/0.63  fof(f96,plain,(
% 1.81/0.63    spl4_3 | spl4_4),
% 1.81/0.63    inference(avatar_split_clause,[],[f50,f94,f91])).
% 1.81/0.63  fof(f50,plain,(
% 1.81/0.63    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.81/0.63    inference(cnf_transformation,[],[f21])).
% 1.81/0.63  fof(f89,plain,(
% 1.81/0.63    spl4_1 | spl4_2),
% 1.81/0.63    inference(avatar_split_clause,[],[f44,f85,f81])).
% 1.81/0.63  fof(f44,plain,(
% 1.81/0.63    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | v3_pre_topc(sK2,sK1)),
% 1.81/0.63    inference(cnf_transformation,[],[f32])).
% 1.81/0.63  fof(f88,plain,(
% 1.81/0.63    ~spl4_1 | ~spl4_2),
% 1.81/0.63    inference(avatar_split_clause,[],[f45,f85,f81])).
% 1.81/0.63  fof(f45,plain,(
% 1.81/0.63    k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~v3_pre_topc(sK2,sK1)),
% 1.81/0.63    inference(cnf_transformation,[],[f32])).
% 1.81/0.63  % SZS output end Proof for theBenchmark
% 1.81/0.63  % (8526)------------------------------
% 1.81/0.63  % (8526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.63  % (8526)Termination reason: Refutation
% 1.81/0.63  
% 1.81/0.63  % (8526)Memory used [KB]: 11769
% 1.81/0.63  % (8526)Time elapsed: 0.207 s
% 1.81/0.63  % (8526)------------------------------
% 1.81/0.63  % (8526)------------------------------
% 2.12/0.63  % (8519)Success in time 0.273 s
%------------------------------------------------------------------------------
