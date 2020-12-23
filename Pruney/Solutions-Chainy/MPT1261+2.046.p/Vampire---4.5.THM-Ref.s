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
% DateTime   : Thu Dec  3 13:11:54 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  196 (3104 expanded)
%              Number of leaves         :   27 ( 950 expanded)
%              Depth                    :   38
%              Number of atoms          :  478 (9258 expanded)
%              Number of equality atoms :  159 (3637 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1820,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f128,f1768,f1774,f1817])).

fof(f1817,plain,
    ( spl3_2
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f1816])).

fof(f1816,plain,
    ( $false
    | spl3_2
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f1812,f126])).

fof(f126,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1812,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f1796,f1804])).

fof(f1804,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f1791,f1803])).

fof(f1803,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1802,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1802,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl3_24 ),
    inference(resolution,[],[f1773,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f83,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1773,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f1771])).

fof(f1771,plain,
    ( spl3_24
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1791,plain,(
    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f785,f77])).

fof(f785,plain,(
    k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f779,f143])).

fof(f143,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f130,f62])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).

fof(f52,plain,
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

fof(f53,plain,
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f130,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f63,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f779,plain,(
    ! [X12] : k1_setfam_1(k2_tarski(X12,sK1)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X12)) ),
    inference(forward_demodulation,[],[f778,f279])).

fof(f279,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ),
    inference(forward_demodulation,[],[f275,f77])).

fof(f275,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) ),
    inference(resolution,[],[f271,f106])).

fof(f271,plain,(
    ! [X8] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X8),sK1) ),
    inference(superposition,[],[f103,f138])).

fof(f138,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X2))) ),
    inference(resolution,[],[f63,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f90,f99])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f81,f78])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f76,f99])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f778,plain,(
    ! [X12] : k1_setfam_1(k2_tarski(X12,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X12)))) ),
    inference(forward_demodulation,[],[f770,f259])).

fof(f259,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1))) ),
    inference(superposition,[],[f138,f77])).

fof(f770,plain,(
    ! [X12] : k1_setfam_1(k2_tarski(X12,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X12,sK1)))))) ),
    inference(superposition,[],[f104,f566])).

fof(f566,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,sK1)) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(X0,sK1)))) ),
    inference(forward_demodulation,[],[f561,f77])).

fof(f561,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,sK1)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,sK1)),sK1)) ),
    inference(resolution,[],[f553,f106])).

fof(f553,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(X0,sK1)),sK1) ),
    inference(superposition,[],[f539,f77])).

fof(f539,plain,(
    ! [X7] : r1_tarski(k1_setfam_1(k2_tarski(sK1,X7)),sK1) ),
    inference(superposition,[],[f271,f273])).

fof(f273,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1)) ),
    inference(forward_demodulation,[],[f264,f138])).

fof(f264,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1)))) ),
    inference(superposition,[],[f138,f104])).

fof(f104,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f80,f78,f99,f99])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1796,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f532,f1791])).

fof(f532,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f273,f143])).

fof(f1774,plain,
    ( spl3_24
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f1769,f120,f1771])).

fof(f120,plain,
    ( spl3_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1769,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f134,f62])).

fof(f134,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f63,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f1768,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f1767])).

fof(f1767,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f1766,f147])).

fof(f147,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f146,f62])).

fof(f146,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f145,f122])).

fof(f122,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f145,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f133,f61])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f133,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f63,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f1766,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f672,f1765])).

fof(f1765,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f1760,f100])).

fof(f100,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1760,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,k1_xboole_0))
    | ~ spl3_2 ),
    inference(superposition,[],[f619,f1453])).

fof(f1453,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f1347,f1434])).

fof(f1434,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f1433,f102])).

fof(f102,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f75,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1433,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) ),
    inference(subsumption_resolution,[],[f1431,f1325])).

fof(f1325,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1314,f358])).

fof(f358,plain,(
    ! [X3] : ~ r2_hidden(X3,k5_xboole_0(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f357,f197])).

fof(f197,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_xboole_0(sK1,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f118,f150])).

fof(f150,plain,(
    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(resolution,[],[f139,f106])).

fof(f139,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f63,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f93,f99])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f58,f59])).

fof(f59,plain,(
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

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f357,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(sK1,sK1))
      | ~ r2_hidden(X3,sK1) ) ),
    inference(superposition,[],[f267,f262])).

fof(f262,plain,(
    k5_xboole_0(sK1,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(superposition,[],[f138,f102])).

fof(f267,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k7_subset_1(u1_struct_0(sK0),sK1,X2))
      | ~ r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f117,f138])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f94,f99])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1314,plain,(
    ! [X2] :
      ( r2_hidden(X2,k5_xboole_0(sK1,sK1))
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f400,f1310])).

fof(f1310,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f1298,f1309])).

fof(f1309,plain,(
    k5_xboole_0(sK1,sK1) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK1),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))) ),
    inference(forward_demodulation,[],[f1306,f100])).

fof(f1306,plain,(
    k3_tarski(k2_tarski(k5_xboole_0(sK1,sK1),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK1),k1_xboole_0)) ),
    inference(superposition,[],[f105,f1302])).

fof(f1302,plain,(
    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1301,f77])).

fof(f1301,plain,(
    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f1300,f106])).

fof(f1300,plain,(
    r1_tarski(k5_xboole_0(sK1,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1293,f404])).

fof(f404,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))) ),
    inference(backward_demodulation,[],[f397,f403])).

fof(f403,plain,(
    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) = k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))) ),
    inference(forward_demodulation,[],[f402,f77])).

fof(f402,plain,(
    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) = k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0)) ),
    inference(resolution,[],[f398,f106])).

fof(f398,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0) ),
    inference(superposition,[],[f103,f387])).

fof(f387,plain,(
    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f382,f77])).

fof(f382,plain,(
    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f280,f263])).

fof(f263,plain,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(superposition,[],[f138,f101])).

fof(f101,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f68,f99])).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f280,plain,(
    ! [X7] : k1_setfam_1(k2_tarski(sK1,X7)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X7)) ),
    inference(backward_demodulation,[],[f270,f279])).

fof(f270,plain,(
    ! [X7] : k1_setfam_1(k2_tarski(sK1,X7)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X7)))) ),
    inference(superposition,[],[f104,f138])).

fof(f397,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))))) ),
    inference(superposition,[],[f104,f387])).

fof(f1293,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))),k1_xboole_0) ),
    inference(superposition,[],[f103,f403])).

fof(f105,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ),
    inference(definition_unfolding,[],[f82,f79,f99,f79])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1298,plain,(
    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK1),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))) ),
    inference(forward_demodulation,[],[f1297,f100])).

fof(f1297,plain,(
    k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0)) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK1),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))) ),
    inference(forward_demodulation,[],[f1296,f77])).

fof(f1296,plain,(
    k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0)) = k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1291,f404])).

fof(f1291,plain,(
    k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0)) = k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))))) ),
    inference(superposition,[],[f105,f403])).

fof(f400,plain,(
    ! [X2] :
      ( r2_hidden(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f395,f354])).

fof(f354,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f267,f263])).

fof(f395,plain,(
    ! [X2] :
      ( r2_hidden(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))
      | r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f116,f387])).

fof(f116,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f95,f99])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1431,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))
      | r2_hidden(sK2(X1,X1,k1_xboole_0),k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f1391])).

fof(f1391,plain,(
    ! [X1] :
      ( k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))
      | k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))
      | r2_hidden(sK2(X1,X1,k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f1341,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f97,f99])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1341,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,k1_xboole_0),X0)
      | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(resolution,[],[f1325,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ) ),
    inference(definition_unfolding,[],[f96,f99])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1347,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f610,f292])).

fof(f292,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f291,f77])).

fof(f291,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f276,f106])).

fof(f276,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f271,f125])).

fof(f125,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f610,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1)))) ),
    inference(superposition,[],[f163,f77])).

fof(f163,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X2) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2))) ),
    inference(resolution,[],[f148,f108])).

fof(f148,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f135,f62])).

fof(f135,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f63,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f619,plain,(
    ! [X6] : k3_tarski(k2_tarski(X6,k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(X6,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X6))) ),
    inference(superposition,[],[f105,f163])).

fof(f672,plain,(
    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f663,f144])).

fof(f144,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f131,f62])).

fof(f131,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f63,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f663,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f161,f63])).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1))) ) ),
    inference(resolution,[],[f148,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f92,f79])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f128,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f64,f124,f120])).

fof(f64,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f127,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f65,f124,f120])).

fof(f65,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:18:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (4153)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (4150)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (4164)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (4154)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (4172)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (4156)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (4168)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (4163)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (4170)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (4162)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (4167)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (4152)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (4148)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (4160)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (4173)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (4178)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (4171)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (4149)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (4151)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (4175)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (4157)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (4176)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (4159)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (4171)Refutation not found, incomplete strategy% (4171)------------------------------
% 0.21/0.54  % (4171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4171)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4171)Memory used [KB]: 10746
% 0.21/0.54  % (4171)Time elapsed: 0.129 s
% 0.21/0.54  % (4171)------------------------------
% 0.21/0.54  % (4171)------------------------------
% 0.21/0.54  % (4165)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (4169)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (4174)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (4161)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (4158)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (4166)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (4166)Refutation not found, incomplete strategy% (4166)------------------------------
% 0.21/0.55  % (4166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4166)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4166)Memory used [KB]: 10618
% 0.21/0.55  % (4166)Time elapsed: 0.148 s
% 0.21/0.55  % (4166)------------------------------
% 0.21/0.55  % (4166)------------------------------
% 1.56/0.57  % (4177)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.02/0.63  % (4157)Refutation found. Thanks to Tanya!
% 2.02/0.63  % SZS status Theorem for theBenchmark
% 2.02/0.63  % SZS output start Proof for theBenchmark
% 2.02/0.63  fof(f1820,plain,(
% 2.02/0.63    $false),
% 2.02/0.63    inference(avatar_sat_refutation,[],[f127,f128,f1768,f1774,f1817])).
% 2.02/0.63  fof(f1817,plain,(
% 2.02/0.63    spl3_2 | ~spl3_24),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f1816])).
% 2.02/0.63  fof(f1816,plain,(
% 2.02/0.63    $false | (spl3_2 | ~spl3_24)),
% 2.02/0.63    inference(subsumption_resolution,[],[f1812,f126])).
% 2.02/0.63  fof(f126,plain,(
% 2.02/0.63    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl3_2),
% 2.02/0.63    inference(avatar_component_clause,[],[f124])).
% 2.02/0.63  fof(f124,plain,(
% 2.02/0.63    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.02/0.63  fof(f1812,plain,(
% 2.02/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl3_24),
% 2.02/0.63    inference(backward_demodulation,[],[f1796,f1804])).
% 2.02/0.63  fof(f1804,plain,(
% 2.02/0.63    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl3_24),
% 2.02/0.63    inference(backward_demodulation,[],[f1791,f1803])).
% 2.02/0.63  fof(f1803,plain,(
% 2.02/0.63    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_24),
% 2.02/0.63    inference(forward_demodulation,[],[f1802,f77])).
% 2.02/0.63  fof(f77,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f10])).
% 2.02/0.63  fof(f10,axiom,(
% 2.02/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.02/0.63  fof(f1802,plain,(
% 2.02/0.63    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl3_24),
% 2.02/0.63    inference(resolution,[],[f1773,f106])).
% 2.02/0.63  fof(f106,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 2.02/0.63    inference(definition_unfolding,[],[f83,f78])).
% 2.02/0.63  fof(f78,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f18])).
% 2.02/0.63  fof(f18,axiom,(
% 2.02/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.02/0.63  fof(f83,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f39])).
% 2.02/0.63  fof(f39,plain,(
% 2.02/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.02/0.63    inference(ennf_transformation,[],[f5])).
% 2.02/0.63  fof(f5,axiom,(
% 2.02/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.02/0.63  fof(f1773,plain,(
% 2.02/0.63    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl3_24),
% 2.02/0.63    inference(avatar_component_clause,[],[f1771])).
% 2.02/0.63  fof(f1771,plain,(
% 2.02/0.63    spl3_24 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.02/0.63  fof(f1791,plain,(
% 2.02/0.63    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.02/0.63    inference(forward_demodulation,[],[f785,f77])).
% 2.02/0.63  fof(f785,plain,(
% 2.02/0.63    k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.02/0.63    inference(superposition,[],[f779,f143])).
% 2.02/0.63  fof(f143,plain,(
% 2.02/0.63    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.02/0.63    inference(subsumption_resolution,[],[f130,f62])).
% 2.02/0.63  fof(f62,plain,(
% 2.02/0.63    l1_pre_topc(sK0)),
% 2.02/0.63    inference(cnf_transformation,[],[f54])).
% 2.02/0.63  fof(f54,plain,(
% 2.02/0.63    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.02/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).
% 2.02/0.63  fof(f52,plain,(
% 2.02/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f53,plain,(
% 2.02/0.63    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f51,plain,(
% 2.02/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.02/0.63    inference(flattening,[],[f50])).
% 2.02/0.63  fof(f50,plain,(
% 2.02/0.63    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.02/0.63    inference(nnf_transformation,[],[f31])).
% 2.02/0.63  fof(f31,plain,(
% 2.02/0.63    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.02/0.63    inference(flattening,[],[f30])).
% 2.02/0.63  fof(f30,plain,(
% 2.02/0.63    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f28])).
% 2.02/0.63  fof(f28,negated_conjecture,(
% 2.02/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.02/0.63    inference(negated_conjecture,[],[f27])).
% 2.02/0.63  fof(f27,conjecture,(
% 2.02/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.02/0.63  fof(f130,plain,(
% 2.02/0.63    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.02/0.63    inference(resolution,[],[f63,f70])).
% 2.02/0.63  fof(f70,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f33])).
% 2.02/0.63  fof(f33,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f26])).
% 2.02/0.63  fof(f26,axiom,(
% 2.02/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.02/0.63  fof(f63,plain,(
% 2.02/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.02/0.63    inference(cnf_transformation,[],[f54])).
% 2.02/0.63  fof(f779,plain,(
% 2.02/0.63    ( ! [X12] : (k1_setfam_1(k2_tarski(X12,sK1)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X12))) )),
% 2.02/0.63    inference(forward_demodulation,[],[f778,f279])).
% 2.02/0.63  fof(f279,plain,(
% 2.02/0.63    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) )),
% 2.02/0.63    inference(forward_demodulation,[],[f275,f77])).
% 2.02/0.63  fof(f275,plain,(
% 2.02/0.63    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1))) )),
% 2.02/0.63    inference(resolution,[],[f271,f106])).
% 2.02/0.63  fof(f271,plain,(
% 2.02/0.63    ( ! [X8] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X8),sK1)) )),
% 2.02/0.63    inference(superposition,[],[f103,f138])).
% 2.02/0.63  fof(f138,plain,(
% 2.02/0.63    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),sK1,X2) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X2)))) )),
% 2.02/0.63    inference(resolution,[],[f63,f108])).
% 2.02/0.63  fof(f108,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 2.02/0.63    inference(definition_unfolding,[],[f90,f99])).
% 2.02/0.63  fof(f99,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.02/0.63    inference(definition_unfolding,[],[f81,f78])).
% 2.02/0.63  fof(f81,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f3])).
% 2.02/0.63  fof(f3,axiom,(
% 2.02/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.02/0.63  fof(f90,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f45])).
% 2.02/0.63  fof(f45,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f16])).
% 2.02/0.63  fof(f16,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.02/0.63  fof(f103,plain,(
% 2.02/0.63    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 2.02/0.63    inference(definition_unfolding,[],[f76,f99])).
% 2.02/0.63  fof(f76,plain,(
% 2.02/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f6])).
% 2.02/0.63  fof(f6,axiom,(
% 2.02/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.02/0.63  fof(f778,plain,(
% 2.02/0.63    ( ! [X12] : (k1_setfam_1(k2_tarski(X12,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X12))))) )),
% 2.02/0.63    inference(forward_demodulation,[],[f770,f259])).
% 2.02/0.63  fof(f259,plain,(
% 2.02/0.63    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X0,sK1)))) )),
% 2.02/0.63    inference(superposition,[],[f138,f77])).
% 2.02/0.63  fof(f770,plain,(
% 2.02/0.63    ( ! [X12] : (k1_setfam_1(k2_tarski(X12,sK1)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(X12,sK1))))))) )),
% 2.02/0.63    inference(superposition,[],[f104,f566])).
% 2.02/0.63  fof(f566,plain,(
% 2.02/0.63    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,sK1)) = k1_setfam_1(k2_tarski(sK1,k1_setfam_1(k2_tarski(X0,sK1))))) )),
% 2.02/0.63    inference(forward_demodulation,[],[f561,f77])).
% 2.02/0.63  fof(f561,plain,(
% 2.02/0.63    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,sK1)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,sK1)),sK1))) )),
% 2.02/0.63    inference(resolution,[],[f553,f106])).
% 2.02/0.63  fof(f553,plain,(
% 2.02/0.63    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(X0,sK1)),sK1)) )),
% 2.02/0.63    inference(superposition,[],[f539,f77])).
% 2.02/0.63  fof(f539,plain,(
% 2.02/0.63    ( ! [X7] : (r1_tarski(k1_setfam_1(k2_tarski(sK1,X7)),sK1)) )),
% 2.02/0.63    inference(superposition,[],[f271,f273])).
% 2.02/0.63  fof(f273,plain,(
% 2.02/0.63    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))) )),
% 2.02/0.63    inference(forward_demodulation,[],[f264,f138])).
% 2.02/0.63  fof(f264,plain,(
% 2.02/0.63    ( ! [X1] : (k1_setfam_1(k2_tarski(sK1,X1)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1))))) )),
% 2.02/0.63    inference(superposition,[],[f138,f104])).
% 2.02/0.63  fof(f104,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 2.02/0.63    inference(definition_unfolding,[],[f80,f78,f99,f99])).
% 2.02/0.63  fof(f80,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f9])).
% 2.02/0.63  fof(f9,axiom,(
% 2.02/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.02/0.63  fof(f1796,plain,(
% 2.02/0.63    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.02/0.63    inference(forward_demodulation,[],[f532,f1791])).
% 2.02/0.63  fof(f532,plain,(
% 2.02/0.63    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.02/0.63    inference(superposition,[],[f273,f143])).
% 2.02/0.63  fof(f1774,plain,(
% 2.02/0.63    spl3_24 | ~spl3_1),
% 2.02/0.63    inference(avatar_split_clause,[],[f1769,f120,f1771])).
% 2.02/0.63  fof(f120,plain,(
% 2.02/0.63    spl3_1 <=> v4_pre_topc(sK1,sK0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.02/0.63  fof(f1769,plain,(
% 2.02/0.63    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.02/0.63    inference(subsumption_resolution,[],[f134,f62])).
% 2.02/0.63  fof(f134,plain,(
% 2.02/0.63    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 2.02/0.63    inference(resolution,[],[f63,f74])).
% 2.02/0.63  fof(f74,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f38])).
% 2.02/0.63  fof(f38,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(flattening,[],[f37])).
% 2.02/0.63  fof(f37,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f25])).
% 2.02/0.63  fof(f25,axiom,(
% 2.02/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 2.02/0.63  fof(f1768,plain,(
% 2.02/0.63    spl3_1 | ~spl3_2),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f1767])).
% 2.02/0.63  fof(f1767,plain,(
% 2.02/0.63    $false | (spl3_1 | ~spl3_2)),
% 2.02/0.63    inference(subsumption_resolution,[],[f1766,f147])).
% 2.02/0.63  fof(f147,plain,(
% 2.02/0.63    sK1 != k2_pre_topc(sK0,sK1) | spl3_1),
% 2.02/0.63    inference(subsumption_resolution,[],[f146,f62])).
% 2.02/0.63  fof(f146,plain,(
% 2.02/0.63    sK1 != k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | spl3_1),
% 2.02/0.63    inference(subsumption_resolution,[],[f145,f122])).
% 2.02/0.63  fof(f122,plain,(
% 2.02/0.63    ~v4_pre_topc(sK1,sK0) | spl3_1),
% 2.02/0.63    inference(avatar_component_clause,[],[f120])).
% 2.02/0.63  fof(f145,plain,(
% 2.02/0.63    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 2.02/0.63    inference(subsumption_resolution,[],[f133,f61])).
% 2.02/0.63  fof(f61,plain,(
% 2.02/0.63    v2_pre_topc(sK0)),
% 2.02/0.63    inference(cnf_transformation,[],[f54])).
% 2.02/0.63  fof(f133,plain,(
% 2.02/0.63    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 2.02/0.63    inference(resolution,[],[f63,f73])).
% 2.02/0.63  fof(f73,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f36])).
% 2.02/0.64  fof(f36,plain,(
% 2.02/0.64    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.64    inference(flattening,[],[f35])).
% 2.02/0.64  fof(f35,plain,(
% 2.02/0.64    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.64    inference(ennf_transformation,[],[f21])).
% 2.02/0.64  fof(f21,axiom,(
% 2.02/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.02/0.64  fof(f1766,plain,(
% 2.02/0.64    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_2),
% 2.02/0.64    inference(backward_demodulation,[],[f672,f1765])).
% 2.02/0.64  fof(f1765,plain,(
% 2.02/0.64    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_2),
% 2.02/0.64    inference(forward_demodulation,[],[f1760,f100])).
% 2.02/0.64  fof(f100,plain,(
% 2.02/0.64    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 2.02/0.64    inference(definition_unfolding,[],[f67,f79])).
% 2.02/0.64  fof(f79,plain,(
% 2.02/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.02/0.64    inference(cnf_transformation,[],[f11])).
% 2.02/0.64  fof(f11,axiom,(
% 2.02/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.02/0.64  fof(f67,plain,(
% 2.02/0.64    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.02/0.64    inference(cnf_transformation,[],[f4])).
% 2.02/0.64  fof(f4,axiom,(
% 2.02/0.64    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.02/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.12/0.64  fof(f1760,plain,(
% 2.12/0.64    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,k1_xboole_0)) | ~spl3_2),
% 2.12/0.64    inference(superposition,[],[f619,f1453])).
% 2.12/0.64  fof(f1453,plain,(
% 2.12/0.64    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | ~spl3_2),
% 2.12/0.64    inference(backward_demodulation,[],[f1347,f1434])).
% 2.12/0.64  fof(f1434,plain,(
% 2.12/0.64    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 2.12/0.64    inference(forward_demodulation,[],[f1433,f102])).
% 2.12/0.64  fof(f102,plain,(
% 2.12/0.64    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 2.12/0.64    inference(definition_unfolding,[],[f75,f78])).
% 2.12/0.64  fof(f75,plain,(
% 2.12/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.12/0.64    inference(cnf_transformation,[],[f29])).
% 2.12/0.64  fof(f29,plain,(
% 2.12/0.64    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.12/0.64    inference(rectify,[],[f2])).
% 2.12/0.64  fof(f2,axiom,(
% 2.12/0.64    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.12/0.64  fof(f1433,plain,(
% 2.12/0.64    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))) )),
% 2.12/0.64    inference(subsumption_resolution,[],[f1431,f1325])).
% 2.12/0.64  fof(f1325,plain,(
% 2.12/0.64    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 2.12/0.64    inference(subsumption_resolution,[],[f1314,f358])).
% 2.12/0.64  fof(f358,plain,(
% 2.12/0.64    ( ! [X3] : (~r2_hidden(X3,k5_xboole_0(sK1,sK1))) )),
% 2.12/0.64    inference(subsumption_resolution,[],[f357,f197])).
% 2.12/0.64  fof(f197,plain,(
% 2.12/0.64    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,sK1)) | r2_hidden(X0,sK1)) )),
% 2.12/0.64    inference(superposition,[],[f118,f150])).
% 2.12/0.64  fof(f150,plain,(
% 2.12/0.64    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))),
% 2.12/0.64    inference(resolution,[],[f139,f106])).
% 2.12/0.64  fof(f139,plain,(
% 2.12/0.64    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.12/0.64    inference(resolution,[],[f63,f88])).
% 2.12/0.64  fof(f88,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f55])).
% 2.12/0.64  fof(f55,plain,(
% 2.12/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.12/0.64    inference(nnf_transformation,[],[f19])).
% 2.12/0.64  fof(f19,axiom,(
% 2.12/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.12/0.64  fof(f118,plain,(
% 2.12/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | r2_hidden(X4,X0)) )),
% 2.12/0.64    inference(equality_resolution,[],[f115])).
% 2.12/0.64  fof(f115,plain,(
% 2.12/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.12/0.64    inference(definition_unfolding,[],[f93,f99])).
% 2.12/0.64  fof(f93,plain,(
% 2.12/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.12/0.64    inference(cnf_transformation,[],[f60])).
% 2.12/0.64  fof(f60,plain,(
% 2.12/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.12/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f58,f59])).
% 2.12/0.64  fof(f59,plain,(
% 2.12/0.64    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.12/0.64    introduced(choice_axiom,[])).
% 2.12/0.64  fof(f58,plain,(
% 2.12/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.12/0.64    inference(rectify,[],[f57])).
% 2.12/0.64  fof(f57,plain,(
% 2.12/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.12/0.64    inference(flattening,[],[f56])).
% 2.12/0.64  fof(f56,plain,(
% 2.12/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.12/0.64    inference(nnf_transformation,[],[f1])).
% 2.12/0.64  fof(f1,axiom,(
% 2.12/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.12/0.64  fof(f357,plain,(
% 2.12/0.64    ( ! [X3] : (~r2_hidden(X3,k5_xboole_0(sK1,sK1)) | ~r2_hidden(X3,sK1)) )),
% 2.12/0.64    inference(superposition,[],[f267,f262])).
% 2.12/0.64  fof(f262,plain,(
% 2.12/0.64    k5_xboole_0(sK1,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 2.12/0.64    inference(superposition,[],[f138,f102])).
% 2.12/0.64  fof(f267,plain,(
% 2.12/0.64    ( ! [X2,X3] : (~r2_hidden(X3,k7_subset_1(u1_struct_0(sK0),sK1,X2)) | ~r2_hidden(X3,X2)) )),
% 2.12/0.64    inference(superposition,[],[f117,f138])).
% 2.12/0.64  fof(f117,plain,(
% 2.12/0.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | ~r2_hidden(X4,X1)) )),
% 2.12/0.64    inference(equality_resolution,[],[f114])).
% 2.12/0.64  fof(f114,plain,(
% 2.12/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.12/0.64    inference(definition_unfolding,[],[f94,f99])).
% 2.12/0.64  fof(f94,plain,(
% 2.12/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.12/0.64    inference(cnf_transformation,[],[f60])).
% 2.12/0.64  fof(f1314,plain,(
% 2.12/0.64    ( ! [X2] : (r2_hidden(X2,k5_xboole_0(sK1,sK1)) | ~r2_hidden(X2,k1_xboole_0)) )),
% 2.12/0.64    inference(backward_demodulation,[],[f400,f1310])).
% 2.12/0.64  fof(f1310,plain,(
% 2.12/0.64    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))),
% 2.12/0.64    inference(backward_demodulation,[],[f1298,f1309])).
% 2.12/0.64  fof(f1309,plain,(
% 2.12/0.64    k5_xboole_0(sK1,sK1) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK1),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))))),
% 2.12/0.64    inference(forward_demodulation,[],[f1306,f100])).
% 2.12/0.64  fof(f1306,plain,(
% 2.12/0.64    k3_tarski(k2_tarski(k5_xboole_0(sK1,sK1),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK1),k1_xboole_0))),
% 2.12/0.64    inference(superposition,[],[f105,f1302])).
% 2.12/0.64  fof(f1302,plain,(
% 2.12/0.64    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(sK1,sK1)))),
% 2.12/0.64    inference(forward_demodulation,[],[f1301,f77])).
% 2.12/0.64  fof(f1301,plain,(
% 2.12/0.64    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(k5_xboole_0(sK1,sK1),k1_xboole_0))),
% 2.12/0.64    inference(resolution,[],[f1300,f106])).
% 2.12/0.64  fof(f1300,plain,(
% 2.12/0.64    r1_tarski(k5_xboole_0(sK1,sK1),k1_xboole_0)),
% 2.12/0.64    inference(forward_demodulation,[],[f1293,f404])).
% 2.12/0.64  fof(f404,plain,(
% 2.12/0.64    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))),
% 2.12/0.64    inference(backward_demodulation,[],[f397,f403])).
% 2.12/0.64  fof(f403,plain,(
% 2.12/0.64    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) = k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))))),
% 2.12/0.64    inference(forward_demodulation,[],[f402,f77])).
% 2.12/0.64  fof(f402,plain,(
% 2.12/0.64    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) = k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0))),
% 2.12/0.64    inference(resolution,[],[f398,f106])).
% 2.12/0.64  fof(f398,plain,(
% 2.12/0.64    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0)),
% 2.12/0.64    inference(superposition,[],[f103,f387])).
% 2.12/0.64  fof(f387,plain,(
% 2.12/0.64    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(k1_xboole_0,sK1))),
% 2.12/0.64    inference(forward_demodulation,[],[f382,f77])).
% 2.12/0.64  fof(f382,plain,(
% 2.12/0.64    k5_xboole_0(sK1,sK1) = k1_setfam_1(k2_tarski(sK1,k1_xboole_0))),
% 2.12/0.64    inference(superposition,[],[f280,f263])).
% 2.12/0.64  fof(f263,plain,(
% 2.12/0.64    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)),
% 2.12/0.64    inference(superposition,[],[f138,f101])).
% 2.12/0.64  fof(f101,plain,(
% 2.12/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 2.12/0.64    inference(definition_unfolding,[],[f68,f99])).
% 2.12/0.64  fof(f68,plain,(
% 2.12/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.12/0.64    inference(cnf_transformation,[],[f8])).
% 2.12/0.64  fof(f8,axiom,(
% 2.12/0.64    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.12/0.64  fof(f280,plain,(
% 2.12/0.64    ( ! [X7] : (k1_setfam_1(k2_tarski(sK1,X7)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X7))) )),
% 2.12/0.64    inference(backward_demodulation,[],[f270,f279])).
% 2.12/0.64  fof(f270,plain,(
% 2.12/0.64    ( ! [X7] : (k1_setfam_1(k2_tarski(sK1,X7)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X7))))) )),
% 2.12/0.64    inference(superposition,[],[f104,f138])).
% 2.12/0.64  fof(f397,plain,(
% 2.12/0.64    k5_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))))),
% 2.12/0.64    inference(superposition,[],[f104,f387])).
% 2.12/0.64  fof(f1293,plain,(
% 2.12/0.64    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))),k1_xboole_0)),
% 2.12/0.64    inference(superposition,[],[f103,f403])).
% 2.12/0.64  fof(f105,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))) )),
% 2.12/0.64    inference(definition_unfolding,[],[f82,f79,f99,f79])).
% 2.12/0.64  fof(f82,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f7])).
% 2.12/0.64  fof(f7,axiom,(
% 2.12/0.64    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.12/0.64  fof(f1298,plain,(
% 2.12/0.64    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK1),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))))),
% 2.12/0.64    inference(forward_demodulation,[],[f1297,f100])).
% 2.12/0.64  fof(f1297,plain,(
% 2.12/0.64    k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0)) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK1),k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))))),
% 2.12/0.64    inference(forward_demodulation,[],[f1296,f77])).
% 2.12/0.64  fof(f1296,plain,(
% 2.12/0.64    k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0)) = k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1)))),
% 2.12/0.64    inference(forward_demodulation,[],[f1291,f404])).
% 2.12/0.64  fof(f1291,plain,(
% 2.12/0.64    k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k1_xboole_0)) = k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)),k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)))))),
% 2.12/0.64    inference(superposition,[],[f105,f403])).
% 2.12/0.64  fof(f400,plain,(
% 2.12/0.64    ( ! [X2] : (r2_hidden(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))) | ~r2_hidden(X2,k1_xboole_0)) )),
% 2.12/0.64    inference(subsumption_resolution,[],[f395,f354])).
% 2.12/0.64  fof(f354,plain,(
% 2.12/0.64    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 2.12/0.64    inference(superposition,[],[f267,f263])).
% 2.12/0.64  fof(f395,plain,(
% 2.12/0.64    ( ! [X2] : (r2_hidden(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))) | r2_hidden(X2,sK1) | ~r2_hidden(X2,k1_xboole_0)) )),
% 2.12/0.64    inference(superposition,[],[f116,f387])).
% 2.12/0.64  fof(f116,plain,(
% 2.12/0.64    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.12/0.64    inference(equality_resolution,[],[f113])).
% 2.12/0.64  fof(f113,plain,(
% 2.12/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.12/0.64    inference(definition_unfolding,[],[f95,f99])).
% 2.12/0.64  fof(f95,plain,(
% 2.12/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.12/0.64    inference(cnf_transformation,[],[f60])).
% 2.12/0.64  fof(f1431,plain,(
% 2.12/0.64    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) | r2_hidden(sK2(X1,X1,k1_xboole_0),k1_xboole_0)) )),
% 2.12/0.64    inference(duplicate_literal_removal,[],[f1391])).
% 2.12/0.64  fof(f1391,plain,(
% 2.12/0.64    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) | k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) | r2_hidden(sK2(X1,X1,k1_xboole_0),k1_xboole_0)) )),
% 2.12/0.64    inference(resolution,[],[f1341,f111])).
% 2.12/0.64  fof(f111,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.12/0.64    inference(definition_unfolding,[],[f97,f99])).
% 2.12/0.64  fof(f97,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f60])).
% 2.12/0.64  fof(f1341,plain,(
% 2.12/0.64    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k1_xboole_0),X0) | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.12/0.64    inference(resolution,[],[f1325,f112])).
% 2.12/0.64  fof(f112,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2) )),
% 2.12/0.64    inference(definition_unfolding,[],[f96,f99])).
% 2.12/0.64  fof(f96,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f60])).
% 2.12/0.64  fof(f1347,plain,(
% 2.12/0.64    k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | ~spl3_2),
% 2.12/0.64    inference(superposition,[],[f610,f292])).
% 2.12/0.64  fof(f292,plain,(
% 2.12/0.64    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_2),
% 2.12/0.64    inference(forward_demodulation,[],[f291,f77])).
% 2.12/0.64  fof(f291,plain,(
% 2.12/0.64    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl3_2),
% 2.12/0.64    inference(resolution,[],[f276,f106])).
% 2.12/0.64  fof(f276,plain,(
% 2.12/0.64    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl3_2),
% 2.12/0.64    inference(superposition,[],[f271,f125])).
% 2.12/0.64  fof(f125,plain,(
% 2.12/0.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl3_2),
% 2.12/0.64    inference(avatar_component_clause,[],[f124])).
% 2.12/0.64  fof(f610,plain,(
% 2.12/0.64    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))))) )),
% 2.12/0.64    inference(superposition,[],[f163,f77])).
% 2.12/0.64  fof(f163,plain,(
% 2.12/0.64    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X2) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X2)))) )),
% 2.12/0.64    inference(resolution,[],[f148,f108])).
% 2.12/0.64  fof(f148,plain,(
% 2.12/0.64    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.12/0.64    inference(subsumption_resolution,[],[f135,f62])).
% 2.12/0.64  fof(f135,plain,(
% 2.12/0.64    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.12/0.64    inference(resolution,[],[f63,f87])).
% 2.12/0.64  fof(f87,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f44])).
% 2.12/0.64  fof(f44,plain,(
% 2.12/0.64    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(flattening,[],[f43])).
% 2.12/0.64  fof(f43,plain,(
% 2.12/0.64    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.12/0.64    inference(ennf_transformation,[],[f22])).
% 2.12/0.64  fof(f22,axiom,(
% 2.12/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.12/0.64  fof(f619,plain,(
% 2.12/0.64    ( ! [X6] : (k3_tarski(k2_tarski(X6,k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(X6,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X6)))) )),
% 2.12/0.64    inference(superposition,[],[f105,f163])).
% 2.12/0.64  fof(f672,plain,(
% 2.12/0.64    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.12/0.64    inference(forward_demodulation,[],[f663,f144])).
% 2.12/0.64  fof(f144,plain,(
% 2.12/0.64    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.12/0.64    inference(subsumption_resolution,[],[f131,f62])).
% 2.12/0.64  fof(f131,plain,(
% 2.12/0.64    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.12/0.64    inference(resolution,[],[f63,f71])).
% 2.12/0.64  fof(f71,plain,(
% 2.12/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f34])).
% 2.12/0.64  fof(f34,plain,(
% 2.12/0.64    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.12/0.64    inference(ennf_transformation,[],[f24])).
% 2.12/0.64  fof(f24,axiom,(
% 2.12/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.12/0.64  fof(f663,plain,(
% 2.12/0.64    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.12/0.64    inference(resolution,[],[f161,f63])).
% 2.12/0.64  fof(f161,plain,(
% 2.12/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1)))) )),
% 2.12/0.64    inference(resolution,[],[f148,f109])).
% 2.12/0.64  fof(f109,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.12/0.64    inference(definition_unfolding,[],[f92,f79])).
% 2.12/0.64  fof(f92,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f49])).
% 2.12/0.64  fof(f49,plain,(
% 2.12/0.64    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.12/0.64    inference(flattening,[],[f48])).
% 2.12/0.64  fof(f48,plain,(
% 2.12/0.64    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.12/0.64    inference(ennf_transformation,[],[f15])).
% 2.12/0.64  fof(f15,axiom,(
% 2.12/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.12/0.64  fof(f128,plain,(
% 2.12/0.64    spl3_1 | spl3_2),
% 2.12/0.64    inference(avatar_split_clause,[],[f64,f124,f120])).
% 2.12/0.64  fof(f64,plain,(
% 2.12/0.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.12/0.64    inference(cnf_transformation,[],[f54])).
% 2.12/0.64  fof(f127,plain,(
% 2.12/0.64    ~spl3_1 | ~spl3_2),
% 2.12/0.64    inference(avatar_split_clause,[],[f65,f124,f120])).
% 2.12/0.64  fof(f65,plain,(
% 2.12/0.64    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.12/0.64    inference(cnf_transformation,[],[f54])).
% 2.12/0.64  % SZS output end Proof for theBenchmark
% 2.12/0.64  % (4157)------------------------------
% 2.12/0.64  % (4157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.64  % (4157)Termination reason: Refutation
% 2.12/0.64  
% 2.12/0.64  % (4157)Memory used [KB]: 11897
% 2.12/0.64  % (4157)Time elapsed: 0.227 s
% 2.12/0.64  % (4157)------------------------------
% 2.12/0.64  % (4157)------------------------------
% 2.12/0.64  % (4144)Success in time 0.283 s
%------------------------------------------------------------------------------
