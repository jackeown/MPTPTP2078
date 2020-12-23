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
% DateTime   : Thu Dec  3 13:11:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 411 expanded)
%              Number of leaves         :   31 ( 129 expanded)
%              Depth                    :   20
%              Number of atoms          :  338 (1475 expanded)
%              Number of equality atoms :  104 ( 474 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f1786,f1788,f1790,f1793,f1796,f1802,f2381])).

fof(f2381,plain,
    ( spl2_2
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f2380])).

fof(f2380,plain,
    ( $false
    | spl2_2
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f2368])).

fof(f2368,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | spl2_2
    | ~ spl2_6 ),
    inference(superposition,[],[f1862,f2303])).

fof(f2303,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f2294,f1808])).

fof(f1808,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f1806,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1806,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_6 ),
    inference(resolution,[],[f1801,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f79,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1801,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f1799])).

fof(f1799,plain,
    ( spl2_6
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f2294,plain,(
    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f95,f2289])).

fof(f2289,plain,(
    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f2281,f538])).

fof(f538,plain,(
    ! [X20] : k7_subset_1(u1_struct_0(sK0),sK1,X20) = k6_subset_1(sK1,X20) ),
    inference(resolution,[],[f100,f59])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f54,f53])).

fof(f53,plain,
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

fof(f54,plain,
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

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f87,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f2281,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f2195,f59])).

fof(f2195,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f67,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f95,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f76,f75,f73,f73])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1862,plain,
    ( k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(superposition,[],[f133,f538])).

fof(f133,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1802,plain,
    ( spl2_6
    | ~ spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f1795,f128,f1783,f1799])).

fof(f1783,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f128,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1795,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f130,f1058])).

fof(f1058,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f68,f58])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f130,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f128])).

fof(f1796,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f1794])).

fof(f1794,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f130,f137])).

fof(f137,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f61,f134])).

fof(f134,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f61,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f1793,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f1791])).

fof(f1791,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f1785,f59])).

fof(f1785,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f1783])).

fof(f1790,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f1789])).

fof(f1789,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f1781,f58])).

fof(f1781,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f1779,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1788,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f1787])).

fof(f1787,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f1777,f57])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f1777,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f1775])).

fof(f1775,plain,
    ( spl2_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1786,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f1772,f132,f128,f1783,f1779,f1775])).

fof(f1772,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f83,f1771])).

fof(f1771,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1763,f1536])).

fof(f1536,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1530,f550])).

fof(f550,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f410,f540])).

fof(f540,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(superposition,[],[f538,f134])).

fof(f410,plain,(
    ! [X6,X5] : k3_tarski(k2_tarski(X5,k6_subset_1(X5,X6))) = X5 ),
    inference(forward_demodulation,[],[f399,f91])).

fof(f91,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f63,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f63,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f399,plain,(
    ! [X6,X5] : k3_tarski(k2_tarski(X5,k6_subset_1(X5,X6))) = k3_tarski(k2_tarski(X5,k1_xboole_0)) ),
    inference(superposition,[],[f97,f264])).

fof(f264,plain,(
    ! [X2,X3] : k1_xboole_0 = k6_subset_1(k6_subset_1(X2,X3),X2) ),
    inference(forward_demodulation,[],[f259,f211])).

fof(f211,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f207,f147])).

fof(f147,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f142,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f142,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k6_subset_1(X0,X0) ),
    inference(superposition,[],[f95,f92])).

fof(f92,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f64,f73])).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f207,plain,(
    ! [X1] : k6_subset_1(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f96,f93])).

fof(f93,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f69,f75])).

fof(f69,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f96,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f77,f73,f75])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f259,plain,(
    ! [X2,X3] : k6_subset_1(k6_subset_1(X2,X3),X2) = k5_xboole_0(k6_subset_1(X2,X3),k6_subset_1(X2,X3)) ),
    inference(superposition,[],[f204,f126])).

fof(f126,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k6_subset_1(X0,X1))) ),
    inference(forward_demodulation,[],[f122,f72])).

fof(f122,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),X0)) ),
    inference(resolution,[],[f98,f94])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f204,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f96,f72])).

fof(f97,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f78,f74,f73,f74])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1530,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f1513,f713])).

fof(f713,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f145,f586])).

fof(f586,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f584,f72])).

fof(f584,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(resolution,[],[f581,f98])).

fof(f581,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(resolution,[],[f546,f112])).

fof(f112,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f85,f59])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f546,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k2_tops_1(sK0,sK1),X0) )
    | ~ spl2_2 ),
    inference(superposition,[],[f116,f540])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f88,f94])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f145,plain,(
    ! [X4,X3] : m1_subset_1(k1_setfam_1(k2_tarski(X3,X4)),k1_zfmisc_1(X3)) ),
    inference(superposition,[],[f71,f95])).

fof(f71,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f1513,plain,(
    ! [X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK1,X32) = k3_tarski(k2_tarski(sK1,X32)) ) ),
    inference(resolution,[],[f101,f59])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f89,f74])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1763,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f1746,f59])).

fof(f1746,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f66,f58])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f135,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f60,f132,f128])).

fof(f60,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:27:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (3556)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (3550)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (3553)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (3548)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (3554)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (3557)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (3558)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (3546)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (3549)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (3544)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (3552)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (3547)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (3555)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (3545)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (3551)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (3559)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (3560)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (3561)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.54  % (3546)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f2388,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f135,f1786,f1788,f1790,f1793,f1796,f1802,f2381])).
% 0.22/0.54  fof(f2381,plain,(
% 0.22/0.54    spl2_2 | ~spl2_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f2380])).
% 0.22/0.54  fof(f2380,plain,(
% 0.22/0.54    $false | (spl2_2 | ~spl2_6)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f2368])).
% 0.22/0.54  fof(f2368,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | (spl2_2 | ~spl2_6)),
% 0.22/0.54    inference(superposition,[],[f1862,f2303])).
% 0.22/0.54  fof(f2303,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 0.22/0.54    inference(forward_demodulation,[],[f2294,f1808])).
% 0.22/0.54  fof(f1808,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_6),
% 0.22/0.54    inference(forward_demodulation,[],[f1806,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.54  fof(f1806,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl2_6),
% 0.22/0.54    inference(resolution,[],[f1801,f98])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.22/0.54    inference(definition_unfolding,[],[f79,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.54  fof(f1801,plain,(
% 0.22/0.54    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f1799])).
% 0.22/0.54  fof(f1799,plain,(
% 0.22/0.54    spl2_6 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.54  fof(f2294,plain,(
% 0.22/0.54    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.54    inference(superposition,[],[f95,f2289])).
% 0.22/0.54  fof(f2289,plain,(
% 0.22/0.54    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.54    inference(superposition,[],[f2281,f538])).
% 0.22/0.54  fof(f538,plain,(
% 0.22/0.54    ( ! [X20] : (k7_subset_1(u1_struct_0(sK0),sK1,X20) = k6_subset_1(sK1,X20)) )),
% 0.22/0.54    inference(resolution,[],[f100,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f54,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f28])).
% 0.22/0.54  fof(f28,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f87,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.54  fof(f2281,plain,(
% 0.22/0.54    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.54    inference(resolution,[],[f2195,f59])).
% 0.22/0.54  fof(f2195,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 0.22/0.54    inference(resolution,[],[f67,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f55])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f76,f75,f73,f73])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.54  fof(f1862,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 0.22/0.54    inference(superposition,[],[f133,f538])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f132])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.54  fof(f1802,plain,(
% 0.22/0.54    spl2_6 | ~spl2_5 | ~spl2_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f1795,f128,f1783,f1799])).
% 0.22/0.54  fof(f1783,plain,(
% 0.22/0.54    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.54  fof(f1795,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_1),
% 0.22/0.54    inference(resolution,[],[f130,f1058])).
% 0.22/0.54  fof(f1058,plain,(
% 0.22/0.54    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,X0),X0)) )),
% 0.22/0.54    inference(resolution,[],[f68,f58])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    v4_pre_topc(sK1,sK0) | ~spl2_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f128])).
% 0.22/0.54  fof(f1796,plain,(
% 0.22/0.54    ~spl2_1 | ~spl2_2),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1794])).
% 0.22/0.54  fof(f1794,plain,(
% 0.22/0.54    $false | (~spl2_1 | ~spl2_2)),
% 0.22/0.54    inference(resolution,[],[f130,f137])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    ~v4_pre_topc(sK1,sK0) | ~spl2_2),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f136])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~spl2_2),
% 0.22/0.54    inference(forward_demodulation,[],[f61,f134])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f132])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f55])).
% 0.22/0.54  fof(f1793,plain,(
% 0.22/0.54    spl2_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1791])).
% 0.22/0.54  fof(f1791,plain,(
% 0.22/0.54    $false | spl2_5),
% 0.22/0.54    inference(resolution,[],[f1785,f59])).
% 0.22/0.54  fof(f1785,plain,(
% 0.22/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f1783])).
% 0.22/0.54  fof(f1790,plain,(
% 0.22/0.54    spl2_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1789])).
% 0.22/0.54  fof(f1789,plain,(
% 0.22/0.54    $false | spl2_4),
% 0.22/0.54    inference(resolution,[],[f1781,f58])).
% 0.22/0.54  fof(f1781,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | spl2_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f1779])).
% 0.22/0.54  fof(f1779,plain,(
% 0.22/0.54    spl2_4 <=> l1_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.54  fof(f1788,plain,(
% 0.22/0.54    spl2_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1787])).
% 0.22/0.54  fof(f1787,plain,(
% 0.22/0.54    $false | spl2_3),
% 0.22/0.54    inference(resolution,[],[f1777,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f55])).
% 0.22/0.54  fof(f1777,plain,(
% 0.22/0.54    ~v2_pre_topc(sK0) | spl2_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f1775])).
% 0.22/0.54  fof(f1775,plain,(
% 0.22/0.54    spl2_3 <=> v2_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.54  fof(f1786,plain,(
% 0.22/0.54    ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_1 | ~spl2_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f1772,f132,f128,f1783,f1779,f1775])).
% 0.22/0.54  fof(f1772,plain,(
% 0.22/0.54    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_2),
% 0.22/0.54    inference(superposition,[],[f83,f1771])).
% 0.22/0.54  fof(f1771,plain,(
% 0.22/0.54    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_2),
% 0.22/0.54    inference(forward_demodulation,[],[f1763,f1536])).
% 0.22/0.54  fof(f1536,plain,(
% 0.22/0.54    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.22/0.54    inference(forward_demodulation,[],[f1530,f550])).
% 0.22/0.54  fof(f550,plain,(
% 0.22/0.54    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 0.22/0.54    inference(superposition,[],[f410,f540])).
% 0.22/0.54  fof(f540,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.22/0.54    inference(superposition,[],[f538,f134])).
% 0.22/0.54  fof(f410,plain,(
% 0.22/0.54    ( ! [X6,X5] : (k3_tarski(k2_tarski(X5,k6_subset_1(X5,X6))) = X5) )),
% 0.22/0.54    inference(forward_demodulation,[],[f399,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 0.22/0.54    inference(definition_unfolding,[],[f63,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.54  fof(f399,plain,(
% 0.22/0.54    ( ! [X6,X5] : (k3_tarski(k2_tarski(X5,k6_subset_1(X5,X6))) = k3_tarski(k2_tarski(X5,k1_xboole_0))) )),
% 0.22/0.54    inference(superposition,[],[f97,f264])).
% 0.22/0.54  fof(f264,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k1_xboole_0 = k6_subset_1(k6_subset_1(X2,X3),X2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f259,f211])).
% 0.22/0.54  fof(f211,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f207,f147])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f142,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f62,f75])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k6_subset_1(X0,X0)) )),
% 0.22/0.54    inference(superposition,[],[f95,f92])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(definition_unfolding,[],[f64,f73])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    ( ! [X1] : (k6_subset_1(X1,X1) = k5_xboole_0(X1,X1)) )),
% 0.22/0.54    inference(superposition,[],[f96,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 0.22/0.54    inference(definition_unfolding,[],[f69,f75])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.54    inference(rectify,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f77,f73,f75])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f259,plain,(
% 0.22/0.54    ( ! [X2,X3] : (k6_subset_1(k6_subset_1(X2,X3),X2) = k5_xboole_0(k6_subset_1(X2,X3),k6_subset_1(X2,X3))) )),
% 0.22/0.54    inference(superposition,[],[f204,f126])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k6_subset_1(X0,X1)))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f122,f72])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),X0))) )),
% 0.22/0.54    inference(resolution,[],[f98,f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f70,f73])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))) )),
% 0.22/0.54    inference(superposition,[],[f96,f72])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f78,f74,f73,f74])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.54  fof(f1530,plain,(
% 0.22/0.54    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.22/0.54    inference(resolution,[],[f1513,f713])).
% 0.22/0.54  fof(f713,plain,(
% 0.22/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.22/0.54    inference(superposition,[],[f145,f586])).
% 0.22/0.54  fof(f586,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_2),
% 0.22/0.54    inference(forward_demodulation,[],[f584,f72])).
% 0.22/0.54  fof(f584,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))) | ~spl2_2),
% 0.22/0.54    inference(resolution,[],[f581,f98])).
% 0.22/0.54  fof(f581,plain,(
% 0.22/0.54    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_2),
% 0.22/0.54    inference(resolution,[],[f546,f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f85,f59])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f546,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k2_tops_1(sK0,sK1),X0)) ) | ~spl2_2),
% 0.22/0.54    inference(superposition,[],[f116,f540])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f88,f94])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    ( ! [X4,X3] : (m1_subset_1(k1_setfam_1(k2_tarski(X3,X4)),k1_zfmisc_1(X3))) )),
% 0.22/0.54    inference(superposition,[],[f71,f95])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.22/0.54  fof(f1513,plain,(
% 0.22/0.54    ( ! [X32] : (~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X32) = k3_tarski(k2_tarski(sK1,X32))) )),
% 0.22/0.54    inference(resolution,[],[f101,f59])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f89,f74])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(flattening,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.54  fof(f1763,plain,(
% 0.22/0.54    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)),
% 0.22/0.54    inference(resolution,[],[f1746,f59])).
% 0.22/0.54  fof(f1746,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 0.22/0.54    inference(resolution,[],[f66,f58])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    spl2_1 | spl2_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f60,f132,f128])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f55])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (3546)------------------------------
% 0.22/0.54  % (3546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3546)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (3546)Memory used [KB]: 7036
% 0.22/0.54  % (3546)Time elapsed: 0.126 s
% 0.22/0.54  % (3546)------------------------------
% 0.22/0.54  % (3546)------------------------------
% 0.22/0.54  % (3543)Success in time 0.18 s
%------------------------------------------------------------------------------
