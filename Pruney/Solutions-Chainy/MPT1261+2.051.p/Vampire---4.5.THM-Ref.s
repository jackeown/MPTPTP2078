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
% DateTime   : Thu Dec  3 13:11:55 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 572 expanded)
%              Number of leaves         :   30 ( 185 expanded)
%              Depth                    :   20
%              Number of atoms          :  438 (1830 expanded)
%              Number of equality atoms :  127 ( 638 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f101,f1233,f1528,f1541,f1745,f1754,f1759,f1770,f2234])).

fof(f2234,plain,
    ( ~ spl2_11
    | ~ spl2_12
    | spl2_22
    | ~ spl2_24 ),
    inference(avatar_contradiction_clause,[],[f2233])).

fof(f2233,plain,
    ( $false
    | ~ spl2_11
    | ~ spl2_12
    | spl2_22
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f2232,f53])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).

fof(f48,plain,
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

fof(f49,plain,
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

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f2232,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_11
    | ~ spl2_12
    | spl2_22
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f2231,f54])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f2231,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_11
    | ~ spl2_12
    | spl2_22
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f2224,f1525])).

fof(f1525,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_22 ),
    inference(avatar_component_clause,[],[f1523])).

fof(f1523,plain,
    ( spl2_22
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f2224,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(superposition,[],[f443,f2131])).

fof(f2131,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f2130,f108])).

fof(f108,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f84,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f57,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f58,f82])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f71,f68])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f2130,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f2119,f361])).

fof(f361,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f360,f85])).

fof(f85,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f64,f68])).

fof(f64,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f360,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) ),
    inference(forward_demodulation,[],[f343,f108])).

fof(f343,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_xboole_0)))) ),
    inference(superposition,[],[f88,f83])).

fof(f88,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f70,f68,f82,f82])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2119,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(superposition,[],[f130,f2109])).

fof(f2109,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f2108,f2032])).

fof(f2032,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(backward_demodulation,[],[f1740,f2016])).

fof(f2016,plain,
    ( k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f2015,f1243])).

fof(f1243,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f1236,f1222])).

fof(f1222,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f1221])).

fof(f1221,plain,
    ( spl2_11
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f1236,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_12 ),
    inference(superposition,[],[f74,f1227])).

fof(f1227,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f1225])).

fof(f1225,plain,
    ( spl2_12
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2015,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f2002,f1242])).

fof(f1242,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f1235,f1222])).

fof(f1235,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_12 ),
    inference(superposition,[],[f72,f1227])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f2002,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_24 ),
    inference(superposition,[],[f1868,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f73,f82])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1868,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
    | ~ spl2_24 ),
    inference(superposition,[],[f88,f1740])).

fof(f1740,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f1738])).

fof(f1738,plain,
    ( spl2_24
  <=> k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f2108,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f2099,f2016])).

fof(f2099,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(superposition,[],[f88,f2030])).

fof(f2030,plain,
    ( k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(backward_demodulation,[],[f1868,f2016])).

fof(f130,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(superposition,[],[f87,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f87,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f69,f67,f82])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f443,plain,(
    ! [X2,X3] :
      ( k3_tarski(k2_tarski(X3,k2_tops_1(X2,X3))) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f442,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f442,plain,(
    ! [X2,X3] :
      ( k3_tarski(k2_tarski(X3,k2_tops_1(X2,X3))) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f439])).

fof(f439,plain,(
    ! [X2,X3] :
      ( k3_tarski(k2_tarski(X3,k2_tops_1(X2,X3))) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f60,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f81,f67])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f1770,plain,
    ( ~ spl2_22
    | spl2_1 ),
    inference(avatar_split_clause,[],[f1769,f93,f1523])).

fof(f93,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1769,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f1768,f53])).

fof(f1768,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f1767,f95])).

fof(f95,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1767,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1763,f52])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f1763,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f1759,plain,(
    ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f1755])).

fof(f1755,plain,
    ( $false
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f54,f1736])).

fof(f1736,plain,
    ( ! [X6] : ~ m1_subset_1(sK1,k1_zfmisc_1(X6))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f1735])).

fof(f1735,plain,
    ( spl2_23
  <=> ! [X6] : ~ m1_subset_1(sK1,k1_zfmisc_1(X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f1754,plain,
    ( spl2_2
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f1753,f1523,f97])).

fof(f97,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1753,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f1752,f53])).

fof(f1752,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f1749,f54])).

fof(f1749,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_22 ),
    inference(superposition,[],[f61,f1524])).

fof(f1524,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f1523])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1745,plain,
    ( spl2_23
    | spl2_24
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f1744,f97,f1738,f1735])).

fof(f1744,plain,
    ( ! [X1] :
        ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X1)) )
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1724,f66])).

fof(f1724,plain,
    ( ! [X1] :
        ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X1)) )
    | ~ spl2_2 ),
    inference(duplicate_literal_removal,[],[f1711])).

fof(f1711,plain,
    ( ! [X1] :
        ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X1)) )
    | ~ spl2_2 ),
    inference(superposition,[],[f291,f1701])).

fof(f1701,plain,
    ( ! [X3] :
        ( k2_tops_1(sK0,sK1) = k7_subset_1(X3,sK1,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X3)) )
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1580,f54])).

fof(f1580,plain,
    ( ! [X3] :
        ( k2_tops_1(sK0,sK1) = k7_subset_1(X3,sK1,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X3))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2 ),
    inference(superposition,[],[f296,f98])).

fof(f98,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f296,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_subset_1(X2,X0,X1) = k7_subset_1(X3,X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f90,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f80,f82])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f291,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f90,f66])).

fof(f1541,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f1540,f1221,f97,f1225])).

fof(f1540,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f1539,f1222])).

fof(f1539,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1533,f54])).

fof(f1533,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_2 ),
    inference(superposition,[],[f297,f98])).

fof(f297,plain,(
    ! [X6,X4,X5] :
      ( k3_subset_1(X4,X5) = k7_subset_1(X6,X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) ) ),
    inference(superposition,[],[f90,f89])).

fof(f1528,plain,
    ( spl2_22
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f1527,f93,f1523])).

fof(f1527,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f274,f53])).

fof(f274,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f62,f54])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1233,plain,(
    spl2_11 ),
    inference(avatar_contradiction_clause,[],[f1232])).

fof(f1232,plain,
    ( $false
    | spl2_11 ),
    inference(subsumption_resolution,[],[f1231,f129])).

fof(f129,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f126,f53])).

fof(f126,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f54])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f1231,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | spl2_11 ),
    inference(resolution,[],[f1223,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1223,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f1221])).

fof(f101,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f55,f97,f93])).

fof(f55,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f56,f97,f93])).

fof(f56,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:21:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (9388)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (9402)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (9394)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (9392)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.53  % (9398)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.53  % (9410)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.53  % (9410)Refutation not found, incomplete strategy% (9410)------------------------------
% 1.27/0.53  % (9410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (9389)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.53  % (9396)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.54  % (9401)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.54  % (9397)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.54  % (9414)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.54  % (9413)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.54  % (9410)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (9410)Memory used [KB]: 10746
% 1.27/0.54  % (9410)Time elapsed: 0.113 s
% 1.27/0.54  % (9410)------------------------------
% 1.27/0.54  % (9410)------------------------------
% 1.27/0.54  % (9391)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.55  % (9411)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.55  % (9415)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (9407)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % (9406)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.56  % (9403)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.56  % (9405)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.56  % (9390)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.56  % (9393)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.41/0.56  % (9409)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.56  % (9399)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.57  % (9404)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.57  % (9395)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.57  % (9417)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.57  % (9416)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.57  % (9400)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.57  % (9412)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.58  % (9405)Refutation not found, incomplete strategy% (9405)------------------------------
% 1.41/0.58  % (9405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (9405)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.41/0.58  % (9405)Memory used [KB]: 10618
% 1.41/0.58  % (9405)Time elapsed: 0.167 s
% 1.41/0.58  % (9405)------------------------------
% 1.41/0.58  % (9405)------------------------------
% 1.41/0.59  % (9408)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.99/0.65  % (9425)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.99/0.66  % (9415)Refutation found. Thanks to Tanya!
% 1.99/0.66  % SZS status Theorem for theBenchmark
% 1.99/0.66  % SZS output start Proof for theBenchmark
% 1.99/0.66  fof(f2235,plain,(
% 1.99/0.66    $false),
% 1.99/0.66    inference(avatar_sat_refutation,[],[f100,f101,f1233,f1528,f1541,f1745,f1754,f1759,f1770,f2234])).
% 1.99/0.66  fof(f2234,plain,(
% 1.99/0.66    ~spl2_11 | ~spl2_12 | spl2_22 | ~spl2_24),
% 1.99/0.66    inference(avatar_contradiction_clause,[],[f2233])).
% 1.99/0.66  fof(f2233,plain,(
% 1.99/0.66    $false | (~spl2_11 | ~spl2_12 | spl2_22 | ~spl2_24)),
% 1.99/0.66    inference(subsumption_resolution,[],[f2232,f53])).
% 1.99/0.66  fof(f53,plain,(
% 1.99/0.66    l1_pre_topc(sK0)),
% 1.99/0.66    inference(cnf_transformation,[],[f50])).
% 1.99/0.66  fof(f50,plain,(
% 1.99/0.66    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.99/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).
% 1.99/0.66  fof(f48,plain,(
% 1.99/0.66    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.99/0.66    introduced(choice_axiom,[])).
% 1.99/0.66  fof(f49,plain,(
% 1.99/0.66    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.99/0.66    introduced(choice_axiom,[])).
% 1.99/0.66  fof(f47,plain,(
% 1.99/0.66    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.99/0.66    inference(flattening,[],[f46])).
% 1.99/0.66  fof(f46,plain,(
% 1.99/0.66    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.99/0.66    inference(nnf_transformation,[],[f28])).
% 1.99/0.66  fof(f28,plain,(
% 1.99/0.66    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.99/0.66    inference(flattening,[],[f27])).
% 1.99/0.66  fof(f27,plain,(
% 1.99/0.66    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.99/0.66    inference(ennf_transformation,[],[f25])).
% 1.99/0.66  fof(f25,negated_conjecture,(
% 1.99/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.99/0.66    inference(negated_conjecture,[],[f24])).
% 1.99/0.66  fof(f24,conjecture,(
% 1.99/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 1.99/0.66  fof(f2232,plain,(
% 1.99/0.66    ~l1_pre_topc(sK0) | (~spl2_11 | ~spl2_12 | spl2_22 | ~spl2_24)),
% 1.99/0.66    inference(subsumption_resolution,[],[f2231,f54])).
% 1.99/0.66  fof(f54,plain,(
% 1.99/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.99/0.66    inference(cnf_transformation,[],[f50])).
% 1.99/0.66  fof(f2231,plain,(
% 1.99/0.66    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_11 | ~spl2_12 | spl2_22 | ~spl2_24)),
% 1.99/0.66    inference(subsumption_resolution,[],[f2224,f1525])).
% 1.99/0.66  fof(f1525,plain,(
% 1.99/0.66    sK1 != k2_pre_topc(sK0,sK1) | spl2_22),
% 1.99/0.66    inference(avatar_component_clause,[],[f1523])).
% 1.99/0.66  fof(f1523,plain,(
% 1.99/0.66    spl2_22 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.99/0.66  fof(f2224,plain,(
% 1.99/0.66    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_11 | ~spl2_12 | ~spl2_24)),
% 1.99/0.66    inference(superposition,[],[f443,f2131])).
% 1.99/0.66  fof(f2131,plain,(
% 1.99/0.66    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_11 | ~spl2_12 | ~spl2_24)),
% 1.99/0.66    inference(forward_demodulation,[],[f2130,f108])).
% 1.99/0.66  fof(f108,plain,(
% 1.99/0.66    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.99/0.66    inference(forward_demodulation,[],[f84,f83])).
% 1.99/0.66  fof(f83,plain,(
% 1.99/0.66    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f57,f68])).
% 1.99/0.66  fof(f68,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f16])).
% 1.99/0.66  fof(f16,axiom,(
% 1.99/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.99/0.66  fof(f57,plain,(
% 1.99/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f3])).
% 1.99/0.66  fof(f3,axiom,(
% 1.99/0.66    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.99/0.66  fof(f84,plain,(
% 1.99/0.66    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 1.99/0.66    inference(definition_unfolding,[],[f58,f82])).
% 1.99/0.66  fof(f82,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f71,f68])).
% 1.99/0.66  fof(f71,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f2])).
% 1.99/0.66  fof(f2,axiom,(
% 1.99/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.99/0.66  fof(f58,plain,(
% 1.99/0.66    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.99/0.66    inference(cnf_transformation,[],[f5])).
% 1.99/0.66  fof(f5,axiom,(
% 1.99/0.66    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.99/0.66  fof(f2130,plain,(
% 1.99/0.66    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_xboole_0) | (~spl2_11 | ~spl2_12 | ~spl2_24)),
% 1.99/0.66    inference(forward_demodulation,[],[f2119,f361])).
% 1.99/0.66  fof(f361,plain,(
% 1.99/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.99/0.66    inference(forward_demodulation,[],[f360,f85])).
% 1.99/0.66  fof(f85,plain,(
% 1.99/0.66    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.99/0.66    inference(definition_unfolding,[],[f64,f68])).
% 1.99/0.66  fof(f64,plain,(
% 1.99/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.99/0.66    inference(cnf_transformation,[],[f26])).
% 1.99/0.66  fof(f26,plain,(
% 1.99/0.66    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.99/0.66    inference(rectify,[],[f1])).
% 1.99/0.66  fof(f1,axiom,(
% 1.99/0.66    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.99/0.66  fof(f360,plain,(
% 1.99/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))) )),
% 1.99/0.66    inference(forward_demodulation,[],[f343,f108])).
% 1.99/0.66  fof(f343,plain,(
% 1.99/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_xboole_0))))) )),
% 1.99/0.66    inference(superposition,[],[f88,f83])).
% 1.99/0.66  fof(f88,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f70,f68,f82,f82])).
% 1.99/0.66  fof(f70,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f6])).
% 1.99/0.66  fof(f6,axiom,(
% 1.99/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.99/0.66  fof(f2119,plain,(
% 1.99/0.66    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) | (~spl2_11 | ~spl2_12 | ~spl2_24)),
% 1.99/0.66    inference(superposition,[],[f130,f2109])).
% 1.99/0.66  fof(f2109,plain,(
% 1.99/0.66    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_11 | ~spl2_12 | ~spl2_24)),
% 1.99/0.66    inference(forward_demodulation,[],[f2108,f2032])).
% 1.99/0.66  fof(f2032,plain,(
% 1.99/0.66    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_11 | ~spl2_12 | ~spl2_24)),
% 1.99/0.66    inference(backward_demodulation,[],[f1740,f2016])).
% 1.99/0.66  fof(f2016,plain,(
% 1.99/0.66    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) | (~spl2_11 | ~spl2_12 | ~spl2_24)),
% 1.99/0.66    inference(forward_demodulation,[],[f2015,f1243])).
% 1.99/0.66  fof(f1243,plain,(
% 1.99/0.66    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_11 | ~spl2_12)),
% 1.99/0.66    inference(subsumption_resolution,[],[f1236,f1222])).
% 1.99/0.66  fof(f1222,plain,(
% 1.99/0.66    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_11),
% 1.99/0.66    inference(avatar_component_clause,[],[f1221])).
% 1.99/0.66  fof(f1221,plain,(
% 1.99/0.66    spl2_11 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.99/0.66  fof(f1236,plain,(
% 1.99/0.66    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_12),
% 1.99/0.66    inference(superposition,[],[f74,f1227])).
% 1.99/0.66  fof(f1227,plain,(
% 1.99/0.66    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_12),
% 1.99/0.66    inference(avatar_component_clause,[],[f1225])).
% 1.99/0.66  fof(f1225,plain,(
% 1.99/0.66    spl2_12 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.99/0.66  fof(f74,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f36])).
% 1.99/0.66  fof(f36,plain,(
% 1.99/0.66    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.66    inference(ennf_transformation,[],[f12])).
% 1.99/0.66  fof(f12,axiom,(
% 1.99/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.99/0.66  fof(f2015,plain,(
% 1.99/0.66    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_11 | ~spl2_12 | ~spl2_24)),
% 1.99/0.66    inference(subsumption_resolution,[],[f2002,f1242])).
% 1.99/0.66  fof(f1242,plain,(
% 1.99/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_11 | ~spl2_12)),
% 1.99/0.66    inference(subsumption_resolution,[],[f1235,f1222])).
% 1.99/0.66  fof(f1235,plain,(
% 1.99/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_12),
% 1.99/0.66    inference(superposition,[],[f72,f1227])).
% 1.99/0.66  fof(f72,plain,(
% 1.99/0.66    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f34])).
% 1.99/0.66  fof(f34,plain,(
% 1.99/0.66    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.66    inference(ennf_transformation,[],[f11])).
% 1.99/0.66  fof(f11,axiom,(
% 1.99/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.99/0.66  fof(f2002,plain,(
% 1.99/0.66    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_24),
% 1.99/0.66    inference(superposition,[],[f1868,f89])).
% 1.99/0.66  fof(f89,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f73,f82])).
% 1.99/0.66  fof(f73,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f35])).
% 1.99/0.66  fof(f35,plain,(
% 1.99/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.66    inference(ennf_transformation,[],[f10])).
% 1.99/0.66  fof(f10,axiom,(
% 1.99/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.99/0.66  fof(f1868,plain,(
% 1.99/0.66    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | ~spl2_24),
% 1.99/0.66    inference(superposition,[],[f88,f1740])).
% 1.99/0.66  fof(f1740,plain,(
% 1.99/0.66    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) | ~spl2_24),
% 1.99/0.66    inference(avatar_component_clause,[],[f1738])).
% 1.99/0.66  fof(f1738,plain,(
% 1.99/0.66    spl2_24 <=> k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.99/0.66  fof(f2108,plain,(
% 1.99/0.66    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_11 | ~spl2_12 | ~spl2_24)),
% 1.99/0.66    inference(forward_demodulation,[],[f2099,f2016])).
% 1.99/0.66  fof(f2099,plain,(
% 1.99/0.66    k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_11 | ~spl2_12 | ~spl2_24)),
% 1.99/0.66    inference(superposition,[],[f88,f2030])).
% 1.99/0.66  fof(f2030,plain,(
% 1.99/0.66    k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | (~spl2_11 | ~spl2_12 | ~spl2_24)),
% 1.99/0.66    inference(backward_demodulation,[],[f1868,f2016])).
% 1.99/0.66  fof(f130,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 1.99/0.66    inference(superposition,[],[f87,f66])).
% 1.99/0.66  fof(f66,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f8])).
% 1.99/0.66  fof(f8,axiom,(
% 1.99/0.66    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.99/0.66  fof(f87,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f69,f67,f82])).
% 1.99/0.66  fof(f67,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f9])).
% 1.99/0.66  fof(f9,axiom,(
% 1.99/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.99/0.66  fof(f69,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f7])).
% 1.99/0.66  fof(f7,axiom,(
% 1.99/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.99/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.37/0.69  fof(f443,plain,(
% 2.37/0.69    ( ! [X2,X3] : (k3_tarski(k2_tarski(X3,k2_tops_1(X2,X3))) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 2.37/0.69    inference(subsumption_resolution,[],[f442,f77])).
% 2.37/0.69  fof(f77,plain,(
% 2.37/0.69    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.37/0.69    inference(cnf_transformation,[],[f42])).
% 2.37/0.69  fof(f42,plain,(
% 2.37/0.69    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.37/0.69    inference(flattening,[],[f41])).
% 2.37/0.69  fof(f41,plain,(
% 2.37/0.69    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.37/0.69    inference(ennf_transformation,[],[f19])).
% 2.37/0.69  fof(f19,axiom,(
% 2.37/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.37/0.69  fof(f442,plain,(
% 2.37/0.69    ( ! [X2,X3] : (k3_tarski(k2_tarski(X3,k2_tops_1(X2,X3))) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.37/0.69    inference(duplicate_literal_removal,[],[f439])).
% 2.37/0.69  fof(f439,plain,(
% 2.37/0.69    ( ! [X2,X3] : (k3_tarski(k2_tarski(X3,k2_tops_1(X2,X3))) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.37/0.69    inference(superposition,[],[f60,f91])).
% 2.37/0.69  fof(f91,plain,(
% 2.37/0.69    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.37/0.69    inference(definition_unfolding,[],[f81,f67])).
% 2.37/0.69  fof(f81,plain,(
% 2.37/0.69    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.37/0.69    inference(cnf_transformation,[],[f45])).
% 2.37/0.69  fof(f45,plain,(
% 2.37/0.69    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.37/0.69    inference(flattening,[],[f44])).
% 2.37/0.69  fof(f44,plain,(
% 2.37/0.69    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.37/0.69    inference(ennf_transformation,[],[f13])).
% 2.37/0.69  fof(f13,axiom,(
% 2.37/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.37/0.69  fof(f60,plain,(
% 2.37/0.69    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.37/0.69    inference(cnf_transformation,[],[f30])).
% 2.37/0.69  fof(f30,plain,(
% 2.37/0.69    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.37/0.69    inference(ennf_transformation,[],[f23])).
% 2.37/0.69  fof(f23,axiom,(
% 2.37/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.37/0.69  fof(f1770,plain,(
% 2.37/0.69    ~spl2_22 | spl2_1),
% 2.37/0.69    inference(avatar_split_clause,[],[f1769,f93,f1523])).
% 2.37/0.69  fof(f93,plain,(
% 2.37/0.69    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 2.37/0.69    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.37/0.69  fof(f1769,plain,(
% 2.37/0.69    sK1 != k2_pre_topc(sK0,sK1) | spl2_1),
% 2.37/0.69    inference(subsumption_resolution,[],[f1768,f53])).
% 2.37/0.69  fof(f1768,plain,(
% 2.37/0.69    sK1 != k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | spl2_1),
% 2.37/0.69    inference(subsumption_resolution,[],[f1767,f95])).
% 2.37/0.69  fof(f95,plain,(
% 2.37/0.69    ~v4_pre_topc(sK1,sK0) | spl2_1),
% 2.37/0.69    inference(avatar_component_clause,[],[f93])).
% 2.37/0.69  fof(f1767,plain,(
% 2.37/0.69    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 2.37/0.69    inference(subsumption_resolution,[],[f1763,f52])).
% 2.37/0.69  fof(f52,plain,(
% 2.37/0.69    v2_pre_topc(sK0)),
% 2.37/0.69    inference(cnf_transformation,[],[f50])).
% 2.37/0.69  fof(f1763,plain,(
% 2.37/0.69    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 2.37/0.69    inference(resolution,[],[f54,f63])).
% 2.37/0.69  fof(f63,plain,(
% 2.37/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.37/0.69    inference(cnf_transformation,[],[f33])).
% 2.37/0.69  fof(f33,plain,(
% 2.37/0.69    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.37/0.69    inference(flattening,[],[f32])).
% 2.37/0.69  fof(f32,plain,(
% 2.37/0.69    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.37/0.69    inference(ennf_transformation,[],[f18])).
% 2.37/0.69  fof(f18,axiom,(
% 2.37/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.37/0.69  fof(f1759,plain,(
% 2.37/0.69    ~spl2_23),
% 2.37/0.69    inference(avatar_contradiction_clause,[],[f1755])).
% 2.37/0.69  fof(f1755,plain,(
% 2.37/0.69    $false | ~spl2_23),
% 2.37/0.69    inference(subsumption_resolution,[],[f54,f1736])).
% 2.37/0.69  fof(f1736,plain,(
% 2.37/0.69    ( ! [X6] : (~m1_subset_1(sK1,k1_zfmisc_1(X6))) ) | ~spl2_23),
% 2.37/0.69    inference(avatar_component_clause,[],[f1735])).
% 2.37/0.69  fof(f1735,plain,(
% 2.37/0.69    spl2_23 <=> ! [X6] : ~m1_subset_1(sK1,k1_zfmisc_1(X6))),
% 2.37/0.69    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 2.37/0.69  fof(f1754,plain,(
% 2.37/0.69    spl2_2 | ~spl2_22),
% 2.37/0.69    inference(avatar_split_clause,[],[f1753,f1523,f97])).
% 2.37/0.69  fof(f97,plain,(
% 2.37/0.69    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.37/0.69    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.37/0.69  fof(f1753,plain,(
% 2.37/0.69    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_22),
% 2.37/0.69    inference(subsumption_resolution,[],[f1752,f53])).
% 2.37/0.69  fof(f1752,plain,(
% 2.37/0.69    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_22),
% 2.37/0.69    inference(subsumption_resolution,[],[f1749,f54])).
% 2.37/0.69  fof(f1749,plain,(
% 2.37/0.69    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_22),
% 2.37/0.69    inference(superposition,[],[f61,f1524])).
% 2.37/0.69  fof(f1524,plain,(
% 2.37/0.69    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_22),
% 2.37/0.69    inference(avatar_component_clause,[],[f1523])).
% 2.37/0.69  fof(f61,plain,(
% 2.37/0.69    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.37/0.69    inference(cnf_transformation,[],[f31])).
% 2.37/0.69  fof(f31,plain,(
% 2.37/0.69    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.37/0.69    inference(ennf_transformation,[],[f21])).
% 2.37/0.69  fof(f21,axiom,(
% 2.37/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.37/0.69  fof(f1745,plain,(
% 2.37/0.69    spl2_23 | spl2_24 | ~spl2_2),
% 2.37/0.69    inference(avatar_split_clause,[],[f1744,f97,f1738,f1735])).
% 2.37/0.69  fof(f1744,plain,(
% 2.37/0.69    ( ! [X1] : (k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(X1))) ) | ~spl2_2),
% 2.37/0.69    inference(forward_demodulation,[],[f1724,f66])).
% 2.37/0.69  fof(f1724,plain,(
% 2.37/0.69    ( ! [X1] : (k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(X1))) ) | ~spl2_2),
% 2.37/0.69    inference(duplicate_literal_removal,[],[f1711])).
% 2.37/0.69  fof(f1711,plain,(
% 2.37/0.69    ( ! [X1] : (k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(X1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X1))) ) | ~spl2_2),
% 2.37/0.69    inference(superposition,[],[f291,f1701])).
% 2.37/0.69  fof(f1701,plain,(
% 2.37/0.69    ( ! [X3] : (k2_tops_1(sK0,sK1) = k7_subset_1(X3,sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X3))) ) | ~spl2_2),
% 2.37/0.69    inference(subsumption_resolution,[],[f1580,f54])).
% 2.37/0.69  fof(f1580,plain,(
% 2.37/0.69    ( ! [X3] : (k2_tops_1(sK0,sK1) = k7_subset_1(X3,sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(X3)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_2),
% 2.37/0.69    inference(superposition,[],[f296,f98])).
% 2.37/0.69  fof(f98,plain,(
% 2.37/0.69    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 2.37/0.69    inference(avatar_component_clause,[],[f97])).
% 2.37/0.69  fof(f296,plain,(
% 2.37/0.69    ( ! [X2,X0,X3,X1] : (k7_subset_1(X2,X0,X1) = k7_subset_1(X3,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X3)) | ~m1_subset_1(X0,k1_zfmisc_1(X2))) )),
% 2.37/0.69    inference(superposition,[],[f90,f90])).
% 2.37/0.69  fof(f90,plain,(
% 2.37/0.69    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.37/0.69    inference(definition_unfolding,[],[f80,f82])).
% 2.37/0.69  fof(f80,plain,(
% 2.37/0.69    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.37/0.69    inference(cnf_transformation,[],[f43])).
% 2.37/0.69  fof(f43,plain,(
% 2.37/0.69    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.37/0.69    inference(ennf_transformation,[],[f14])).
% 2.37/0.69  fof(f14,axiom,(
% 2.37/0.69    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.37/0.69  fof(f291,plain,(
% 2.37/0.69    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X2,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X2))) )),
% 2.37/0.69    inference(superposition,[],[f90,f66])).
% 2.37/0.69  fof(f1541,plain,(
% 2.37/0.69    spl2_12 | ~spl2_2 | ~spl2_11),
% 2.37/0.69    inference(avatar_split_clause,[],[f1540,f1221,f97,f1225])).
% 2.37/0.69  fof(f1540,plain,(
% 2.37/0.69    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_11)),
% 2.37/0.69    inference(subsumption_resolution,[],[f1539,f1222])).
% 2.37/0.69  fof(f1539,plain,(
% 2.37/0.69    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_2),
% 2.37/0.69    inference(subsumption_resolution,[],[f1533,f54])).
% 2.37/0.69  fof(f1533,plain,(
% 2.37/0.69    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_2),
% 2.37/0.69    inference(superposition,[],[f297,f98])).
% 2.37/0.69  fof(f297,plain,(
% 2.37/0.69    ( ! [X6,X4,X5] : (k3_subset_1(X4,X5) = k7_subset_1(X6,X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(X6)) | ~m1_subset_1(X5,k1_zfmisc_1(X4))) )),
% 2.37/0.69    inference(superposition,[],[f90,f89])).
% 2.37/0.69  fof(f1528,plain,(
% 2.37/0.69    spl2_22 | ~spl2_1),
% 2.37/0.69    inference(avatar_split_clause,[],[f1527,f93,f1523])).
% 2.37/0.69  fof(f1527,plain,(
% 2.37/0.69    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 2.37/0.69    inference(subsumption_resolution,[],[f274,f53])).
% 2.37/0.69  fof(f274,plain,(
% 2.37/0.69    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 2.37/0.69    inference(resolution,[],[f62,f54])).
% 2.37/0.69  fof(f62,plain,(
% 2.37/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 2.37/0.69    inference(cnf_transformation,[],[f33])).
% 2.37/0.69  fof(f1233,plain,(
% 2.37/0.69    spl2_11),
% 2.37/0.69    inference(avatar_contradiction_clause,[],[f1232])).
% 2.37/0.69  fof(f1232,plain,(
% 2.37/0.69    $false | spl2_11),
% 2.37/0.69    inference(subsumption_resolution,[],[f1231,f129])).
% 2.37/0.69  fof(f129,plain,(
% 2.37/0.69    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.37/0.69    inference(subsumption_resolution,[],[f126,f53])).
% 2.37/0.69  fof(f126,plain,(
% 2.37/0.69    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 2.37/0.69    inference(resolution,[],[f59,f54])).
% 2.37/0.69  fof(f59,plain,(
% 2.37/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.37/0.69    inference(cnf_transformation,[],[f29])).
% 2.37/0.69  fof(f29,plain,(
% 2.37/0.69    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.37/0.69    inference(ennf_transformation,[],[f22])).
% 2.37/0.69  fof(f22,axiom,(
% 2.37/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.37/0.69  fof(f1231,plain,(
% 2.37/0.69    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | spl2_11),
% 2.37/0.69    inference(resolution,[],[f1223,f79])).
% 2.37/0.69  fof(f79,plain,(
% 2.37/0.69    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.37/0.69    inference(cnf_transformation,[],[f51])).
% 2.37/0.69  fof(f51,plain,(
% 2.37/0.69    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.37/0.69    inference(nnf_transformation,[],[f17])).
% 2.37/0.69  fof(f17,axiom,(
% 2.37/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.37/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.37/0.69  fof(f1223,plain,(
% 2.37/0.69    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_11),
% 2.37/0.69    inference(avatar_component_clause,[],[f1221])).
% 2.37/0.69  fof(f101,plain,(
% 2.37/0.69    spl2_1 | spl2_2),
% 2.37/0.69    inference(avatar_split_clause,[],[f55,f97,f93])).
% 2.37/0.69  fof(f55,plain,(
% 2.37/0.69    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.37/0.69    inference(cnf_transformation,[],[f50])).
% 2.37/0.69  fof(f100,plain,(
% 2.37/0.69    ~spl2_1 | ~spl2_2),
% 2.37/0.69    inference(avatar_split_clause,[],[f56,f97,f93])).
% 2.37/0.69  fof(f56,plain,(
% 2.37/0.69    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.37/0.69    inference(cnf_transformation,[],[f50])).
% 2.37/0.69  % SZS output end Proof for theBenchmark
% 2.37/0.69  % (9415)------------------------------
% 2.37/0.69  % (9415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.37/0.69  % (9415)Termination reason: Refutation
% 2.37/0.69  
% 2.37/0.69  % (9415)Memory used [KB]: 7164
% 2.37/0.69  % (9415)Time elapsed: 0.256 s
% 2.37/0.69  % (9415)------------------------------
% 2.37/0.69  % (9415)------------------------------
% 2.37/0.69  % (9387)Success in time 0.321 s
%------------------------------------------------------------------------------
