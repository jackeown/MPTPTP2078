%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:01 EST 2020

% Result     : Theorem 2.66s
% Output     : Refutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 631 expanded)
%              Number of leaves         :   33 ( 194 expanded)
%              Depth                    :   16
%              Number of atoms          :  500 (1706 expanded)
%              Number of equality atoms :  104 ( 478 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2711,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f123,f128,f161,f218,f249,f659,f917,f922,f932,f1003,f1184,f2695,f2697,f2710])).

fof(f2710,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | spl2_25 ),
    inference(avatar_contradiction_clause,[],[f2709])).

fof(f2709,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | spl2_25 ),
    inference(subsumption_resolution,[],[f1001,f2708])).

fof(f2708,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f1177,f213])).

fof(f213,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1177,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f290,f127])).

fof(f127,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | r1_tarski(k2_tops_1(sK0,X0),X0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f78,f122])).

fof(f122,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f1001,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_25 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f1000,plain,
    ( spl2_25
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f2697,plain,
    ( ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(avatar_contradiction_clause,[],[f2696])).

fof(f2696,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f213,f2688])).

fof(f2688,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f2687,f2677])).

fof(f2677,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(backward_demodulation,[],[f1928,f2673])).

fof(f2673,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(backward_demodulation,[],[f1521,f2671])).

fof(f2671,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(backward_demodulation,[],[f1929,f975])).

fof(f975,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_24 ),
    inference(superposition,[],[f326,f931])).

fof(f931,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f929])).

fof(f929,plain,
    ( spl2_24
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f326,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f291,f293])).

fof(f293,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f141,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f98,f103])).

fof(f103,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f85,f83])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f141,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f112,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f112,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
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

fof(f291,plain,
    ( ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f127,f110])).

fof(f1929,plain,
    ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_25 ),
    inference(resolution,[],[f318,f1002])).

fof(f1002,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) ),
    inference(backward_demodulation,[],[f276,f293])).

fof(f276,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f109,f96])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f90,f103])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1521,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_25 ),
    inference(resolution,[],[f236,f1002])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f91,f96])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1928,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_7 ),
    inference(resolution,[],[f318,f248])).

fof(f248,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl2_7
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f2687,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f68,f326])).

fof(f68,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).

fof(f58,plain,
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

fof(f59,plain,
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

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
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
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f2695,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_24
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(avatar_contradiction_clause,[],[f2694])).

fof(f2694,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_24
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f2693,f2592])).

fof(f2592,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_25
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f2591,f1132])).

fof(f1132,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f1002,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2591,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f2555,f2587])).

fof(f2587,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f969,f2586])).

fof(f2586,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_22
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f2564,f921])).

fof(f921,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f919])).

fof(f919,plain,
    ( spl2_22
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f2564,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_27 ),
    inference(unit_resulting_resolution,[],[f1183,f127,f428])).

fof(f428,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | k2_xboole_0(X0,X1) = k4_subset_1(X2,X0,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f102,f96])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1183,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f1181])).

fof(f1181,plain,
    ( spl2_27
  <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f969,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f944,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f944,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f141,f916,f102])).

fof(f916,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f914])).

fof(f914,plain,
    ( spl2_21
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f2555,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f112,f916,f428])).

fof(f2693,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f1192,f2688])).

fof(f1192,plain,
    ( v4_pre_topc(sK1,sK0)
    | sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f450,f127])).

fof(f450,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) != X0 )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f449,f122])).

fof(f449,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f77,f117])).

fof(f117,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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

fof(f1184,plain,
    ( spl2_27
    | ~ spl2_4
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f1142,f1000,f158,f1181])).

fof(f158,plain,
    ( spl2_4
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1142,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_4
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f160,f1002,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f160,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1003,plain,
    ( spl2_25
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f943,f914,f1000])).

fof(f943,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f916,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f932,plain,
    ( spl2_24
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f460,f125,f120,f929])).

fof(f460,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f122,f127,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f922,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f456,f125,f120,f919])).

fof(f456,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f122,f127,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f917,plain,
    ( spl2_21
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f726,f656,f215,f125,f914])).

fof(f215,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f656,plain,
    ( spl2_16
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f726,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(backward_demodulation,[],[f700,f725])).

fof(f725,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(backward_demodulation,[],[f709,f723])).

fof(f723,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f326,f217])).

fof(f217,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f215])).

fof(f709,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f658,f303])).

fof(f303,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) ),
    inference(backward_demodulation,[],[f109,f293])).

fof(f658,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f656])).

fof(f700,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f658,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f659,plain,
    ( spl2_16
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f351,f246,f656])).

fof(f351,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f248,f96])).

fof(f249,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f241,f125,f120,f246])).

fof(f241,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f122,f127,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f218,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f67,f215,f211])).

fof(f67,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f161,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f136,f125,f158])).

fof(f136,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f127,f95])).

fof(f128,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f66,f125])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f123,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f65,f120])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f118,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f64,f115])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (29093)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (29094)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (29119)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (29111)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (29097)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (29102)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (29103)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (29091)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (29092)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (29095)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (29096)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (29115)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (29107)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (29117)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (29122)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (29121)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (29098)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (29120)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (29109)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (29113)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (29112)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (29114)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (29108)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (29101)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (29105)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (29104)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (29106)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (29118)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (29110)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (29100)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.05/0.64  % (29094)Refutation not found, incomplete strategy% (29094)------------------------------
% 2.05/0.64  % (29094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.64  % (29094)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.64  
% 2.05/0.64  % (29094)Memory used [KB]: 6268
% 2.05/0.64  % (29094)Time elapsed: 0.206 s
% 2.05/0.64  % (29094)------------------------------
% 2.05/0.64  % (29094)------------------------------
% 2.66/0.75  % (29250)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.66/0.76  % (29112)Refutation found. Thanks to Tanya!
% 2.66/0.76  % SZS status Theorem for theBenchmark
% 2.66/0.76  % SZS output start Proof for theBenchmark
% 2.66/0.76  fof(f2711,plain,(
% 2.66/0.76    $false),
% 2.66/0.76    inference(avatar_sat_refutation,[],[f118,f123,f128,f161,f218,f249,f659,f917,f922,f932,f1003,f1184,f2695,f2697,f2710])).
% 2.66/0.76  fof(f2710,plain,(
% 2.66/0.76    ~spl2_2 | ~spl2_3 | ~spl2_5 | spl2_25),
% 2.66/0.76    inference(avatar_contradiction_clause,[],[f2709])).
% 2.66/0.76  fof(f2709,plain,(
% 2.66/0.76    $false | (~spl2_2 | ~spl2_3 | ~spl2_5 | spl2_25)),
% 2.66/0.76    inference(subsumption_resolution,[],[f1001,f2708])).
% 2.66/0.76  fof(f2708,plain,(
% 2.66/0.76    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 2.66/0.76    inference(subsumption_resolution,[],[f1177,f213])).
% 2.66/0.76  fof(f213,plain,(
% 2.66/0.76    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 2.66/0.76    inference(avatar_component_clause,[],[f211])).
% 2.66/0.76  fof(f211,plain,(
% 2.66/0.76    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 2.66/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.66/0.76  fof(f1177,plain,(
% 2.66/0.76    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3)),
% 2.66/0.76    inference(resolution,[],[f290,f127])).
% 2.66/0.76  fof(f127,plain,(
% 2.66/0.76    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.66/0.76    inference(avatar_component_clause,[],[f125])).
% 2.66/0.76  fof(f125,plain,(
% 2.66/0.76    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.66/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.66/0.76  fof(f290,plain,(
% 2.66/0.76    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | r1_tarski(k2_tops_1(sK0,X0),X0)) ) | ~spl2_2),
% 2.66/0.76    inference(resolution,[],[f78,f122])).
% 2.66/0.76  fof(f122,plain,(
% 2.66/0.76    l1_pre_topc(sK0) | ~spl2_2),
% 2.66/0.76    inference(avatar_component_clause,[],[f120])).
% 2.66/0.76  fof(f120,plain,(
% 2.66/0.76    spl2_2 <=> l1_pre_topc(sK0)),
% 2.66/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.66/0.76  fof(f78,plain,(
% 2.66/0.76    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 2.66/0.76    inference(cnf_transformation,[],[f42])).
% 2.66/0.76  fof(f42,plain,(
% 2.66/0.76    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.76    inference(flattening,[],[f41])).
% 2.66/0.76  fof(f41,plain,(
% 2.66/0.76    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.76    inference(ennf_transformation,[],[f29])).
% 2.66/0.76  fof(f29,axiom,(
% 2.66/0.76    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.66/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 2.66/0.76  fof(f1001,plain,(
% 2.66/0.76    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_25),
% 2.66/0.76    inference(avatar_component_clause,[],[f1000])).
% 2.66/0.76  fof(f1000,plain,(
% 2.66/0.76    spl2_25 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.66/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 2.66/0.76  fof(f2697,plain,(
% 2.66/0.76    ~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_24 | ~spl2_25),
% 2.66/0.76    inference(avatar_contradiction_clause,[],[f2696])).
% 2.66/0.76  fof(f2696,plain,(
% 2.66/0.76    $false | (~spl2_3 | ~spl2_5 | ~spl2_7 | ~spl2_24 | ~spl2_25)),
% 2.66/0.76    inference(subsumption_resolution,[],[f213,f2688])).
% 2.66/0.76  fof(f2688,plain,(
% 2.66/0.76    ~v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_7 | ~spl2_24 | ~spl2_25)),
% 2.66/0.76    inference(subsumption_resolution,[],[f2687,f2677])).
% 2.66/0.76  fof(f2677,plain,(
% 2.66/0.76    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_7 | ~spl2_24 | ~spl2_25)),
% 2.66/0.76    inference(backward_demodulation,[],[f1928,f2673])).
% 2.66/0.76  fof(f2673,plain,(
% 2.66/0.76    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_24 | ~spl2_25)),
% 2.66/0.76    inference(backward_demodulation,[],[f1521,f2671])).
% 2.66/0.76  fof(f2671,plain,(
% 2.66/0.76    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_24 | ~spl2_25)),
% 2.66/0.76    inference(backward_demodulation,[],[f1929,f975])).
% 2.66/0.76  fof(f975,plain,(
% 2.66/0.76    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_24)),
% 2.66/0.76    inference(superposition,[],[f326,f931])).
% 2.66/0.76  fof(f931,plain,(
% 2.66/0.76    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_24),
% 2.66/0.76    inference(avatar_component_clause,[],[f929])).
% 2.66/0.76  fof(f929,plain,(
% 2.66/0.76    spl2_24 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.66/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 2.66/0.76  fof(f326,plain,(
% 2.66/0.76    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) ) | ~spl2_3),
% 2.66/0.76    inference(forward_demodulation,[],[f291,f293])).
% 2.66/0.76  fof(f293,plain,(
% 2.66/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1)) )),
% 2.66/0.76    inference(unit_resulting_resolution,[],[f141,f110])).
% 2.66/0.76  fof(f110,plain,(
% 2.66/0.76    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 2.66/0.76    inference(definition_unfolding,[],[f98,f103])).
% 2.66/0.76  fof(f103,plain,(
% 2.66/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.66/0.76    inference(definition_unfolding,[],[f85,f83])).
% 2.66/0.76  fof(f83,plain,(
% 2.66/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.66/0.76    inference(cnf_transformation,[],[f22])).
% 2.66/0.76  fof(f22,axiom,(
% 2.66/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.66/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.66/0.76  fof(f85,plain,(
% 2.66/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.66/0.76    inference(cnf_transformation,[],[f4])).
% 2.66/0.76  fof(f4,axiom,(
% 2.66/0.76    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.66/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.66/0.76  fof(f98,plain,(
% 2.66/0.76    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.66/0.76    inference(cnf_transformation,[],[f48])).
% 2.66/0.76  fof(f48,plain,(
% 2.66/0.76    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/0.76    inference(ennf_transformation,[],[f20])).
% 2.66/0.76  fof(f20,axiom,(
% 2.66/0.76    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.66/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.66/0.76  fof(f141,plain,(
% 2.66/0.76    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.66/0.76    inference(unit_resulting_resolution,[],[f112,f96])).
% 2.66/0.76  fof(f96,plain,(
% 2.66/0.76    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.66/0.76    inference(cnf_transformation,[],[f63])).
% 2.66/0.76  fof(f63,plain,(
% 2.66/0.76    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.66/0.76    inference(nnf_transformation,[],[f23])).
% 2.66/0.76  fof(f23,axiom,(
% 2.66/0.76    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.66/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.66/0.76  fof(f112,plain,(
% 2.66/0.76    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.66/0.76    inference(equality_resolution,[],[f93])).
% 2.66/0.76  fof(f93,plain,(
% 2.66/0.76    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.66/0.76    inference(cnf_transformation,[],[f62])).
% 2.66/0.76  fof(f62,plain,(
% 2.66/0.76    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.66/0.76    inference(flattening,[],[f61])).
% 2.66/0.76  fof(f61,plain,(
% 2.66/0.76    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.66/0.76    inference(nnf_transformation,[],[f3])).
% 2.66/0.76  fof(f3,axiom,(
% 2.66/0.76    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.66/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.66/0.76  fof(f291,plain,(
% 2.66/0.76    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 2.66/0.76    inference(unit_resulting_resolution,[],[f127,f110])).
% 2.66/0.76  fof(f1929,plain,(
% 2.66/0.76    k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_25),
% 2.66/0.76    inference(resolution,[],[f318,f1002])).
% 2.66/0.76  fof(f1002,plain,(
% 2.66/0.76    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_25),
% 2.66/0.76    inference(avatar_component_clause,[],[f1000])).
% 2.66/0.76  fof(f318,plain,(
% 2.66/0.76    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 2.66/0.76    inference(backward_demodulation,[],[f276,f293])).
% 2.66/0.76  fof(f276,plain,(
% 2.66/0.76    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_tarski(X1,X0)) )),
% 2.66/0.76    inference(resolution,[],[f109,f96])).
% 2.66/0.76  fof(f109,plain,(
% 2.66/0.76    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.66/0.76    inference(definition_unfolding,[],[f90,f103])).
% 2.66/0.76  fof(f90,plain,(
% 2.66/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.66/0.76    inference(cnf_transformation,[],[f45])).
% 2.66/0.76  fof(f45,plain,(
% 2.66/0.76    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/0.76    inference(ennf_transformation,[],[f16])).
% 2.66/0.76  fof(f16,axiom,(
% 2.66/0.76    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.66/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.66/0.76  fof(f1521,plain,(
% 2.66/0.76    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_25),
% 2.66/0.76    inference(resolution,[],[f236,f1002])).
% 2.66/0.76  fof(f236,plain,(
% 2.66/0.76    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.66/0.76    inference(resolution,[],[f91,f96])).
% 2.66/0.76  fof(f91,plain,(
% 2.66/0.76    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.66/0.76    inference(cnf_transformation,[],[f46])).
% 2.66/0.76  fof(f46,plain,(
% 2.66/0.76    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/0.76    inference(ennf_transformation,[],[f18])).
% 2.66/0.76  fof(f18,axiom,(
% 2.66/0.76    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.66/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.66/0.76  fof(f1928,plain,(
% 2.66/0.76    k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_7),
% 2.66/0.76    inference(resolution,[],[f318,f248])).
% 2.66/0.76  fof(f248,plain,(
% 2.66/0.76    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_7),
% 2.66/0.76    inference(avatar_component_clause,[],[f246])).
% 2.66/0.76  fof(f246,plain,(
% 2.66/0.76    spl2_7 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.66/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.66/0.76  fof(f2687,plain,(
% 2.66/0.76    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_3),
% 2.66/0.76    inference(forward_demodulation,[],[f68,f326])).
% 2.66/0.76  fof(f68,plain,(
% 2.66/0.76    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.66/0.76    inference(cnf_transformation,[],[f60])).
% 2.66/0.76  fof(f60,plain,(
% 2.66/0.76    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.66/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).
% 2.66/0.76  fof(f58,plain,(
% 2.66/0.76    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.66/0.76    introduced(choice_axiom,[])).
% 2.66/0.76  fof(f59,plain,(
% 2.66/0.76    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.66/0.76    introduced(choice_axiom,[])).
% 2.66/0.76  fof(f57,plain,(
% 2.66/0.76    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.66/0.76    inference(flattening,[],[f56])).
% 2.66/0.76  fof(f56,plain,(
% 2.66/0.76    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.66/0.76    inference(nnf_transformation,[],[f34])).
% 2.66/0.76  fof(f34,plain,(
% 2.66/0.76    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.66/0.76    inference(flattening,[],[f33])).
% 2.66/0.77  fof(f33,plain,(
% 2.66/0.77    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.66/0.77    inference(ennf_transformation,[],[f32])).
% 2.66/0.77  fof(f32,negated_conjecture,(
% 2.66/0.77    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.66/0.77    inference(negated_conjecture,[],[f31])).
% 2.66/0.77  fof(f31,conjecture,(
% 2.66/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.66/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.66/0.77  fof(f2695,plain,(
% 2.66/0.77    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_21 | ~spl2_22 | ~spl2_24 | ~spl2_25 | ~spl2_27),
% 2.66/0.77    inference(avatar_contradiction_clause,[],[f2694])).
% 2.66/0.77  fof(f2694,plain,(
% 2.66/0.77    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_21 | ~spl2_22 | ~spl2_24 | ~spl2_25 | ~spl2_27)),
% 2.66/0.77    inference(subsumption_resolution,[],[f2693,f2592])).
% 2.66/0.77  fof(f2592,plain,(
% 2.66/0.77    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_21 | ~spl2_22 | ~spl2_25 | ~spl2_27)),
% 2.66/0.77    inference(forward_demodulation,[],[f2591,f1132])).
% 2.66/0.77  fof(f1132,plain,(
% 2.66/0.77    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_25),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f1002,f88])).
% 2.66/0.77  fof(f88,plain,(
% 2.66/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.66/0.77    inference(cnf_transformation,[],[f43])).
% 2.66/0.77  fof(f43,plain,(
% 2.66/0.77    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.66/0.77    inference(ennf_transformation,[],[f6])).
% 2.66/0.77  fof(f6,axiom,(
% 2.66/0.77    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.66/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.66/0.77  fof(f2591,plain,(
% 2.66/0.77    k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_21 | ~spl2_22 | ~spl2_27)),
% 2.66/0.77    inference(forward_demodulation,[],[f2555,f2587])).
% 2.66/0.77  fof(f2587,plain,(
% 2.66/0.77    k2_pre_topc(sK0,sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_21 | ~spl2_22 | ~spl2_27)),
% 2.66/0.77    inference(backward_demodulation,[],[f969,f2586])).
% 2.66/0.77  fof(f2586,plain,(
% 2.66/0.77    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_22 | ~spl2_27)),
% 2.66/0.77    inference(forward_demodulation,[],[f2564,f921])).
% 2.66/0.77  fof(f921,plain,(
% 2.66/0.77    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_22),
% 2.66/0.77    inference(avatar_component_clause,[],[f919])).
% 2.66/0.77  fof(f919,plain,(
% 2.66/0.77    spl2_22 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.66/0.77    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 2.66/0.77  fof(f2564,plain,(
% 2.66/0.77    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_27)),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f1183,f127,f428])).
% 2.66/0.77  fof(f428,plain,(
% 2.66/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X2)) | k2_xboole_0(X0,X1) = k4_subset_1(X2,X0,X1) | ~r1_tarski(X1,X2)) )),
% 2.66/0.77    inference(resolution,[],[f102,f96])).
% 2.66/0.77  fof(f102,plain,(
% 2.66/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.66/0.77    inference(cnf_transformation,[],[f55])).
% 2.66/0.77  fof(f55,plain,(
% 2.66/0.77    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/0.77    inference(flattening,[],[f54])).
% 2.66/0.77  fof(f54,plain,(
% 2.66/0.77    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.66/0.77    inference(ennf_transformation,[],[f19])).
% 2.66/0.77  fof(f19,axiom,(
% 2.66/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.66/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.66/0.77  fof(f1183,plain,(
% 2.66/0.77    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_27),
% 2.66/0.77    inference(avatar_component_clause,[],[f1181])).
% 2.66/0.77  fof(f1181,plain,(
% 2.66/0.77    spl2_27 <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 2.66/0.77    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 2.66/0.77  fof(f969,plain,(
% 2.66/0.77    k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_21),
% 2.66/0.77    inference(forward_demodulation,[],[f944,f82])).
% 2.66/0.77  fof(f82,plain,(
% 2.66/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.66/0.77    inference(cnf_transformation,[],[f1])).
% 2.66/0.77  fof(f1,axiom,(
% 2.66/0.77    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.66/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.66/0.77  fof(f944,plain,(
% 2.66/0.77    k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) | ~spl2_21),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f141,f916,f102])).
% 2.66/0.77  fof(f916,plain,(
% 2.66/0.77    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_21),
% 2.66/0.77    inference(avatar_component_clause,[],[f914])).
% 2.66/0.77  fof(f914,plain,(
% 2.66/0.77    spl2_21 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.66/0.77    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 2.66/0.77  fof(f2555,plain,(
% 2.66/0.77    k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) | ~spl2_21),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f112,f916,f428])).
% 2.66/0.77  fof(f2693,plain,(
% 2.66/0.77    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_7 | ~spl2_24 | ~spl2_25)),
% 2.66/0.77    inference(subsumption_resolution,[],[f1192,f2688])).
% 2.66/0.77  fof(f1192,plain,(
% 2.66/0.77    v4_pre_topc(sK1,sK0) | sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.66/0.77    inference(resolution,[],[f450,f127])).
% 2.66/0.77  fof(f450,plain,(
% 2.66/0.77    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) != X0) ) | (~spl2_1 | ~spl2_2)),
% 2.66/0.77    inference(subsumption_resolution,[],[f449,f122])).
% 2.66/0.77  fof(f449,plain,(
% 2.66/0.77    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_1),
% 2.66/0.77    inference(resolution,[],[f77,f117])).
% 2.66/0.77  fof(f117,plain,(
% 2.66/0.77    v2_pre_topc(sK0) | ~spl2_1),
% 2.66/0.77    inference(avatar_component_clause,[],[f115])).
% 2.66/0.77  fof(f115,plain,(
% 2.66/0.77    spl2_1 <=> v2_pre_topc(sK0)),
% 2.66/0.77    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.66/0.77  fof(f77,plain,(
% 2.66/0.77    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.66/0.77    inference(cnf_transformation,[],[f40])).
% 2.66/0.77  fof(f40,plain,(
% 2.66/0.77    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.77    inference(flattening,[],[f39])).
% 2.66/0.77  fof(f39,plain,(
% 2.66/0.77    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.77    inference(ennf_transformation,[],[f25])).
% 2.66/0.77  fof(f25,axiom,(
% 2.66/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.66/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.66/0.77  fof(f1184,plain,(
% 2.66/0.77    spl2_27 | ~spl2_4 | ~spl2_25),
% 2.66/0.77    inference(avatar_split_clause,[],[f1142,f1000,f158,f1181])).
% 2.66/0.77  fof(f158,plain,(
% 2.66/0.77    spl2_4 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 2.66/0.77    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.66/0.77  fof(f1142,plain,(
% 2.66/0.77    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_4 | ~spl2_25)),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f160,f1002,f101])).
% 2.66/0.77  fof(f101,plain,(
% 2.66/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.66/0.77    inference(cnf_transformation,[],[f53])).
% 2.66/0.77  fof(f53,plain,(
% 2.66/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.66/0.77    inference(flattening,[],[f52])).
% 2.66/0.77  fof(f52,plain,(
% 2.66/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.66/0.77    inference(ennf_transformation,[],[f8])).
% 2.66/0.77  fof(f8,axiom,(
% 2.66/0.77    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.66/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.66/0.77  fof(f160,plain,(
% 2.66/0.77    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_4),
% 2.66/0.77    inference(avatar_component_clause,[],[f158])).
% 2.66/0.77  fof(f1003,plain,(
% 2.66/0.77    spl2_25 | ~spl2_21),
% 2.66/0.77    inference(avatar_split_clause,[],[f943,f914,f1000])).
% 2.66/0.77  fof(f943,plain,(
% 2.66/0.77    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_21),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f916,f95])).
% 2.66/0.77  fof(f95,plain,(
% 2.66/0.77    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.66/0.77    inference(cnf_transformation,[],[f63])).
% 2.66/0.77  fof(f932,plain,(
% 2.66/0.77    spl2_24 | ~spl2_2 | ~spl2_3),
% 2.66/0.77    inference(avatar_split_clause,[],[f460,f125,f120,f929])).
% 2.66/0.77  fof(f460,plain,(
% 2.66/0.77    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f122,f127,f75])).
% 2.66/0.77  fof(f75,plain,(
% 2.66/0.77    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.66/0.77    inference(cnf_transformation,[],[f38])).
% 2.66/0.77  fof(f38,plain,(
% 2.66/0.77    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.77    inference(ennf_transformation,[],[f30])).
% 2.66/0.77  fof(f30,axiom,(
% 2.66/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.66/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.66/0.77  fof(f922,plain,(
% 2.66/0.77    spl2_22 | ~spl2_2 | ~spl2_3),
% 2.66/0.77    inference(avatar_split_clause,[],[f456,f125,f120,f919])).
% 2.66/0.77  fof(f456,plain,(
% 2.66/0.77    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f122,f127,f74])).
% 2.66/0.77  fof(f74,plain,(
% 2.66/0.77    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.66/0.77    inference(cnf_transformation,[],[f37])).
% 2.66/0.77  fof(f37,plain,(
% 2.66/0.77    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.77    inference(ennf_transformation,[],[f28])).
% 2.66/0.77  fof(f28,axiom,(
% 2.66/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.66/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.66/0.77  fof(f917,plain,(
% 2.66/0.77    spl2_21 | ~spl2_3 | ~spl2_6 | ~spl2_16),
% 2.66/0.77    inference(avatar_split_clause,[],[f726,f656,f215,f125,f914])).
% 2.66/0.77  fof(f215,plain,(
% 2.66/0.77    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.66/0.77    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.66/0.77  fof(f656,plain,(
% 2.66/0.77    spl2_16 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.66/0.77    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 2.66/0.77  fof(f726,plain,(
% 2.66/0.77    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_3 | ~spl2_6 | ~spl2_16)),
% 2.66/0.77    inference(backward_demodulation,[],[f700,f725])).
% 2.66/0.77  fof(f725,plain,(
% 2.66/0.77    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6 | ~spl2_16)),
% 2.66/0.77    inference(backward_demodulation,[],[f709,f723])).
% 2.66/0.77  fof(f723,plain,(
% 2.66/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 2.66/0.77    inference(superposition,[],[f326,f217])).
% 2.66/0.77  fof(f217,plain,(
% 2.66/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 2.66/0.77    inference(avatar_component_clause,[],[f215])).
% 2.66/0.77  fof(f709,plain,(
% 2.66/0.77    k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_16),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f658,f303])).
% 2.66/0.77  fof(f303,plain,(
% 2.66/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 2.66/0.77    inference(backward_demodulation,[],[f109,f293])).
% 2.66/0.77  fof(f658,plain,(
% 2.66/0.77    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_16),
% 2.66/0.77    inference(avatar_component_clause,[],[f656])).
% 2.66/0.77  fof(f700,plain,(
% 2.66/0.77    m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl2_16),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f658,f89])).
% 2.66/0.77  fof(f89,plain,(
% 2.66/0.77    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.66/0.77    inference(cnf_transformation,[],[f44])).
% 2.66/0.77  fof(f44,plain,(
% 2.66/0.77    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.66/0.77    inference(ennf_transformation,[],[f17])).
% 2.66/0.77  fof(f17,axiom,(
% 2.66/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.66/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.66/0.77  fof(f659,plain,(
% 2.66/0.77    spl2_16 | ~spl2_7),
% 2.66/0.77    inference(avatar_split_clause,[],[f351,f246,f656])).
% 2.66/0.77  fof(f351,plain,(
% 2.66/0.77    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_7),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f248,f96])).
% 2.66/0.77  fof(f249,plain,(
% 2.66/0.77    spl2_7 | ~spl2_2 | ~spl2_3),
% 2.66/0.77    inference(avatar_split_clause,[],[f241,f125,f120,f246])).
% 2.66/0.77  fof(f241,plain,(
% 2.66/0.77    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3)),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f122,f127,f72])).
% 2.66/0.77  fof(f72,plain,(
% 2.66/0.77    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.66/0.77    inference(cnf_transformation,[],[f35])).
% 2.66/0.77  fof(f35,plain,(
% 2.66/0.77    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.66/0.77    inference(ennf_transformation,[],[f26])).
% 2.66/0.77  fof(f26,axiom,(
% 2.66/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.66/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.66/0.77  fof(f218,plain,(
% 2.66/0.77    spl2_5 | spl2_6),
% 2.66/0.77    inference(avatar_split_clause,[],[f67,f215,f211])).
% 2.66/0.77  fof(f67,plain,(
% 2.66/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.66/0.77    inference(cnf_transformation,[],[f60])).
% 2.66/0.77  fof(f161,plain,(
% 2.66/0.77    spl2_4 | ~spl2_3),
% 2.66/0.77    inference(avatar_split_clause,[],[f136,f125,f158])).
% 2.66/0.77  fof(f136,plain,(
% 2.66/0.77    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 2.66/0.77    inference(unit_resulting_resolution,[],[f127,f95])).
% 2.66/0.77  fof(f128,plain,(
% 2.66/0.77    spl2_3),
% 2.66/0.77    inference(avatar_split_clause,[],[f66,f125])).
% 2.66/0.77  fof(f66,plain,(
% 2.66/0.77    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.66/0.77    inference(cnf_transformation,[],[f60])).
% 2.66/0.77  fof(f123,plain,(
% 2.66/0.77    spl2_2),
% 2.66/0.77    inference(avatar_split_clause,[],[f65,f120])).
% 2.66/0.77  fof(f65,plain,(
% 2.66/0.77    l1_pre_topc(sK0)),
% 2.66/0.77    inference(cnf_transformation,[],[f60])).
% 2.66/0.77  fof(f118,plain,(
% 2.66/0.77    spl2_1),
% 2.66/0.77    inference(avatar_split_clause,[],[f64,f115])).
% 2.66/0.77  fof(f64,plain,(
% 2.66/0.77    v2_pre_topc(sK0)),
% 2.66/0.77    inference(cnf_transformation,[],[f60])).
% 2.66/0.77  % SZS output end Proof for theBenchmark
% 2.66/0.77  % (29112)------------------------------
% 2.66/0.77  % (29112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.77  % (29112)Termination reason: Refutation
% 2.66/0.77  
% 2.66/0.77  % (29112)Memory used [KB]: 13176
% 2.66/0.77  % (29112)Time elapsed: 0.341 s
% 2.66/0.77  % (29112)------------------------------
% 2.66/0.77  % (29112)------------------------------
% 2.66/0.77  % (29087)Success in time 0.409 s
%------------------------------------------------------------------------------
