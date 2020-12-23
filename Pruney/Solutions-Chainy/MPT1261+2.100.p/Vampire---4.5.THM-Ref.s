%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:03 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 404 expanded)
%              Number of leaves         :   23 ( 115 expanded)
%              Depth                    :   24
%              Number of atoms          :  324 (1578 expanded)
%              Number of equality atoms :  117 ( 481 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2585,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f94,f2470,f2481,f2584])).

fof(f2584,plain,
    ( spl2_2
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f2583])).

fof(f2583,plain,
    ( $false
    | spl2_2
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f2582,f92])).

fof(f92,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f2582,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f345,f2478])).

fof(f2478,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f2476])).

fof(f2476,plain,
    ( spl2_13
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f345,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f343,f50])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f43,plain,
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

fof(f44,plain,
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

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f343,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f2481,plain,
    ( spl2_13
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f2480,f86,f2476])).

fof(f86,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f2480,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f243,f50])).

fof(f243,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f58,f51])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f2470,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f2469])).

fof(f2469,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f2468,f50])).

fof(f2468,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f2467,f51])).

fof(f2467,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f2466,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f2466,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f2456,f88])).

fof(f88,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f2456,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f2455])).

fof(f2455,plain,
    ( sK1 != sK1
    | v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f59,f2450])).

fof(f2450,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f293,f2431])).

fof(f2431,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f2430,f117])).

fof(f117,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f78,f112])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f100,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f100,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f71,f96])).

fof(f96,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f72,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f78,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f2430,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f2413,f1681])).

fof(f1681,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f1641,f162])).

fof(f162,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(superposition,[],[f158,f91])).

fof(f91,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f158,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f75,f51])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1641,plain,(
    ! [X15,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X16),X15) ),
    inference(forward_demodulation,[],[f1505,f112])).

fof(f1505,plain,(
    ! [X15,X16] : k4_xboole_0(k4_xboole_0(X15,X16),X15) = k4_xboole_0(k1_xboole_0,X16) ),
    inference(superposition,[],[f545,f357])).

fof(f357,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f347,f295])).

fof(f295,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f133,f261])).

fof(f261,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f192,f119])).

fof(f119,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(resolution,[],[f80,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f64,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f192,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f177,f117])).

fof(f177,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0) = k4_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f81,f112])).

fof(f81,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f74,f63])).

fof(f74,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f130,f127])).

fof(f127,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f65,f54])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f130,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f66,f54])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f347,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f128,f83])).

fof(f128,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) ) ),
    inference(resolution,[],[f65,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f545,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(k4_xboole_0(X3,X5),X4) ),
    inference(superposition,[],[f182,f81])).

fof(f182,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f81,f79])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f61,f63,f63])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2413,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f884,f707])).

fof(f707,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f693,f162])).

fof(f693,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(sK1,X2),u1_struct_0(sK0)) ),
    inference(superposition,[],[f190,f672])).

fof(f672,plain,(
    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[],[f348,f132])).

fof(f132,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f129,f126])).

fof(f126,plain,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f65,f51])).

fof(f129,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f66,f51])).

fof(f348,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_subset_1(X1,k4_xboole_0(X1,X2)) ),
    inference(resolution,[],[f128,f60])).

fof(f190,plain,(
    ! [X12,X13,X11] : r1_tarski(k4_xboole_0(k4_xboole_0(X11,X12),X13),X11) ),
    inference(superposition,[],[f60,f81])).

fof(f884,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,u1_struct_0(sK0))
      | k5_xboole_0(sK1,k4_xboole_0(X8,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,X8) ) ),
    inference(resolution,[],[f320,f51])).

fof(f320,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f82,f73])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f77,f63])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f293,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f291,f50])).

fof(f291,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f51])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f52,f90,f86])).

fof(f52,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f53,f90,f86])).

fof(f53,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (22735)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.49  % (22728)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (22740)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (22748)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (22730)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (22743)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (22739)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (22729)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (22736)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (22726)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (22732)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.51  % (22727)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.52  % (22737)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.27/0.52  % (22750)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.27/0.52  % (22755)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.27/0.52  % (22733)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.27/0.52  % (22747)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.27/0.53  % (22752)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.53  % (22744)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.27/0.53  % (22734)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.27/0.53  % (22749)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.53  % (22738)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.27/0.53  % (22731)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.27/0.53  % (22751)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.27/0.53  % (22745)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.27/0.53  % (22755)Refutation not found, incomplete strategy% (22755)------------------------------
% 1.27/0.53  % (22755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (22755)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (22755)Memory used [KB]: 1663
% 1.27/0.53  % (22755)Time elapsed: 0.002 s
% 1.27/0.53  % (22755)------------------------------
% 1.27/0.53  % (22755)------------------------------
% 1.27/0.53  % (22753)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.54  % (22741)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.42/0.54  % (22754)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.42/0.55  % (22746)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.55  % (22742)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.55  % (22742)Refutation not found, incomplete strategy% (22742)------------------------------
% 1.42/0.55  % (22742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (22742)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (22742)Memory used [KB]: 10618
% 1.42/0.55  % (22742)Time elapsed: 0.139 s
% 1.42/0.55  % (22742)------------------------------
% 1.42/0.55  % (22742)------------------------------
% 2.10/0.64  % (22812)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.10/0.65  % (22732)Refutation found. Thanks to Tanya!
% 2.10/0.65  % SZS status Theorem for theBenchmark
% 2.10/0.66  % SZS output start Proof for theBenchmark
% 2.10/0.66  fof(f2585,plain,(
% 2.10/0.66    $false),
% 2.10/0.66    inference(avatar_sat_refutation,[],[f93,f94,f2470,f2481,f2584])).
% 2.10/0.66  fof(f2584,plain,(
% 2.10/0.66    spl2_2 | ~spl2_13),
% 2.10/0.66    inference(avatar_contradiction_clause,[],[f2583])).
% 2.10/0.66  fof(f2583,plain,(
% 2.10/0.66    $false | (spl2_2 | ~spl2_13)),
% 2.10/0.66    inference(subsumption_resolution,[],[f2582,f92])).
% 2.10/0.66  fof(f92,plain,(
% 2.10/0.66    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 2.10/0.66    inference(avatar_component_clause,[],[f90])).
% 2.10/0.66  fof(f90,plain,(
% 2.10/0.66    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.10/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.10/0.66  fof(f2582,plain,(
% 2.10/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_13),
% 2.10/0.66    inference(forward_demodulation,[],[f345,f2478])).
% 2.10/0.66  fof(f2478,plain,(
% 2.10/0.66    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_13),
% 2.10/0.66    inference(avatar_component_clause,[],[f2476])).
% 2.10/0.66  fof(f2476,plain,(
% 2.10/0.66    spl2_13 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 2.10/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 2.10/0.66  fof(f345,plain,(
% 2.10/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.10/0.66    inference(subsumption_resolution,[],[f343,f50])).
% 2.10/0.66  fof(f50,plain,(
% 2.10/0.66    l1_pre_topc(sK0)),
% 2.10/0.66    inference(cnf_transformation,[],[f45])).
% 2.10/0.66  fof(f45,plain,(
% 2.10/0.66    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.10/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 2.10/0.66  fof(f43,plain,(
% 2.10/0.66    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.10/0.66    introduced(choice_axiom,[])).
% 2.10/0.66  fof(f44,plain,(
% 2.10/0.66    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.10/0.66    introduced(choice_axiom,[])).
% 2.10/0.67  fof(f42,plain,(
% 2.10/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.10/0.67    inference(flattening,[],[f41])).
% 2.10/0.67  fof(f41,plain,(
% 2.10/0.67    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.10/0.67    inference(nnf_transformation,[],[f24])).
% 2.10/0.67  fof(f24,plain,(
% 2.10/0.67    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.10/0.67    inference(flattening,[],[f23])).
% 2.10/0.67  fof(f23,plain,(
% 2.10/0.67    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f22])).
% 2.10/0.67  fof(f22,negated_conjecture,(
% 2.10/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.10/0.67    inference(negated_conjecture,[],[f21])).
% 2.10/0.67  fof(f21,conjecture,(
% 2.10/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 2.10/0.67  fof(f343,plain,(
% 2.10/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.10/0.67    inference(resolution,[],[f57,f51])).
% 2.10/0.67  fof(f51,plain,(
% 2.10/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.10/0.67    inference(cnf_transformation,[],[f45])).
% 2.10/0.67  fof(f57,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f26])).
% 2.10/0.67  fof(f26,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.67    inference(ennf_transformation,[],[f19])).
% 2.10/0.67  fof(f19,axiom,(
% 2.10/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.10/0.67  fof(f2481,plain,(
% 2.10/0.67    spl2_13 | ~spl2_1),
% 2.10/0.67    inference(avatar_split_clause,[],[f2480,f86,f2476])).
% 2.10/0.67  fof(f86,plain,(
% 2.10/0.67    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 2.10/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.10/0.67  fof(f2480,plain,(
% 2.10/0.67    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 2.10/0.67    inference(subsumption_resolution,[],[f243,f50])).
% 2.10/0.67  fof(f243,plain,(
% 2.10/0.67    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 2.10/0.67    inference(resolution,[],[f58,f51])).
% 2.10/0.67  fof(f58,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f28])).
% 2.10/0.67  fof(f28,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.67    inference(flattening,[],[f27])).
% 2.10/0.67  fof(f27,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.67    inference(ennf_transformation,[],[f16])).
% 2.10/0.67  fof(f16,axiom,(
% 2.10/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.10/0.67  fof(f2470,plain,(
% 2.10/0.67    spl2_1 | ~spl2_2),
% 2.10/0.67    inference(avatar_contradiction_clause,[],[f2469])).
% 2.10/0.67  fof(f2469,plain,(
% 2.10/0.67    $false | (spl2_1 | ~spl2_2)),
% 2.10/0.67    inference(subsumption_resolution,[],[f2468,f50])).
% 2.10/0.67  fof(f2468,plain,(
% 2.10/0.67    ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_2)),
% 2.10/0.67    inference(subsumption_resolution,[],[f2467,f51])).
% 2.10/0.67  fof(f2467,plain,(
% 2.10/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_2)),
% 2.10/0.67    inference(subsumption_resolution,[],[f2466,f49])).
% 2.10/0.67  fof(f49,plain,(
% 2.10/0.67    v2_pre_topc(sK0)),
% 2.10/0.67    inference(cnf_transformation,[],[f45])).
% 2.10/0.67  fof(f2466,plain,(
% 2.10/0.67    ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_2)),
% 2.10/0.67    inference(subsumption_resolution,[],[f2456,f88])).
% 2.10/0.67  fof(f88,plain,(
% 2.10/0.67    ~v4_pre_topc(sK1,sK0) | spl2_1),
% 2.10/0.67    inference(avatar_component_clause,[],[f86])).
% 2.10/0.67  fof(f2456,plain,(
% 2.10/0.67    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 2.10/0.67    inference(trivial_inequality_removal,[],[f2455])).
% 2.10/0.67  fof(f2455,plain,(
% 2.10/0.67    sK1 != sK1 | v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 2.10/0.67    inference(superposition,[],[f59,f2450])).
% 2.10/0.67  fof(f2450,plain,(
% 2.10/0.67    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_2),
% 2.10/0.67    inference(backward_demodulation,[],[f293,f2431])).
% 2.10/0.67  fof(f2431,plain,(
% 2.10/0.67    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 2.10/0.67    inference(forward_demodulation,[],[f2430,f117])).
% 2.10/0.67  fof(f117,plain,(
% 2.10/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.10/0.67    inference(backward_demodulation,[],[f78,f112])).
% 2.10/0.67  fof(f112,plain,(
% 2.10/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.10/0.67    inference(resolution,[],[f100,f60])).
% 2.10/0.67  fof(f60,plain,(
% 2.10/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f5])).
% 2.10/0.67  fof(f5,axiom,(
% 2.10/0.67    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.10/0.67  fof(f100,plain,(
% 2.10/0.67    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 2.10/0.67    inference(resolution,[],[f71,f96])).
% 2.10/0.67  fof(f96,plain,(
% 2.10/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.10/0.67    inference(resolution,[],[f72,f54])).
% 2.10/0.67  fof(f54,plain,(
% 2.10/0.67    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f13])).
% 2.10/0.67  fof(f13,axiom,(
% 2.10/0.67    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.10/0.67  fof(f72,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f48])).
% 2.10/0.67  fof(f48,plain,(
% 2.10/0.67    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.10/0.67    inference(nnf_transformation,[],[f14])).
% 2.10/0.67  fof(f14,axiom,(
% 2.10/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.10/0.67  fof(f71,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f47])).
% 2.10/0.67  fof(f47,plain,(
% 2.10/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.10/0.67    inference(flattening,[],[f46])).
% 2.10/0.67  fof(f46,plain,(
% 2.10/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.10/0.67    inference(nnf_transformation,[],[f2])).
% 2.10/0.67  fof(f2,axiom,(
% 2.10/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.10/0.67  fof(f78,plain,(
% 2.10/0.67    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 2.10/0.67    inference(definition_unfolding,[],[f55,f63])).
% 2.10/0.67  fof(f63,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f8])).
% 2.10/0.67  fof(f8,axiom,(
% 2.10/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.10/0.67  fof(f55,plain,(
% 2.10/0.67    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.10/0.67    inference(cnf_transformation,[],[f3])).
% 2.10/0.67  fof(f3,axiom,(
% 2.10/0.67    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.10/0.67  fof(f2430,plain,(
% 2.10/0.67    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | ~spl2_2),
% 2.10/0.67    inference(forward_demodulation,[],[f2413,f1681])).
% 2.10/0.67  fof(f1681,plain,(
% 2.10/0.67    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_2),
% 2.10/0.67    inference(superposition,[],[f1641,f162])).
% 2.10/0.67  fof(f162,plain,(
% 2.10/0.67    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 2.10/0.67    inference(superposition,[],[f158,f91])).
% 2.10/0.67  fof(f91,plain,(
% 2.10/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 2.10/0.67    inference(avatar_component_clause,[],[f90])).
% 2.10/0.67  fof(f158,plain,(
% 2.10/0.67    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 2.10/0.67    inference(resolution,[],[f75,f51])).
% 2.10/0.67  fof(f75,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f36])).
% 2.10/0.67  fof(f36,plain,(
% 2.10/0.67    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f12])).
% 2.10/0.67  fof(f12,axiom,(
% 2.10/0.67    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.10/0.67  fof(f1641,plain,(
% 2.10/0.67    ( ! [X15,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X16),X15)) )),
% 2.10/0.67    inference(forward_demodulation,[],[f1505,f112])).
% 2.10/0.67  fof(f1505,plain,(
% 2.10/0.67    ( ! [X15,X16] : (k4_xboole_0(k4_xboole_0(X15,X16),X15) = k4_xboole_0(k1_xboole_0,X16)) )),
% 2.10/0.67    inference(superposition,[],[f545,f357])).
% 2.10/0.67  fof(f357,plain,(
% 2.10/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.10/0.67    inference(forward_demodulation,[],[f347,f295])).
% 2.10/0.67  fof(f295,plain,(
% 2.10/0.67    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 2.10/0.67    inference(backward_demodulation,[],[f133,f261])).
% 2.10/0.67  fof(f261,plain,(
% 2.10/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.10/0.67    inference(superposition,[],[f192,f119])).
% 2.10/0.67  fof(f119,plain,(
% 2.10/0.67    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.10/0.67    inference(resolution,[],[f80,f83])).
% 2.10/0.67  fof(f83,plain,(
% 2.10/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.10/0.67    inference(equality_resolution,[],[f70])).
% 2.10/0.67  fof(f70,plain,(
% 2.10/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.10/0.67    inference(cnf_transformation,[],[f47])).
% 2.10/0.67  fof(f80,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 2.10/0.67    inference(definition_unfolding,[],[f64,f62])).
% 2.10/0.67  fof(f62,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f7])).
% 2.10/0.67  fof(f7,axiom,(
% 2.10/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.10/0.67  fof(f64,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f29])).
% 2.10/0.67  fof(f29,plain,(
% 2.10/0.67    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.10/0.67    inference(ennf_transformation,[],[f4])).
% 2.10/0.67  fof(f4,axiom,(
% 2.10/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.10/0.67  fof(f192,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0)) )),
% 2.10/0.67    inference(forward_demodulation,[],[f177,f117])).
% 2.10/0.67  fof(f177,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0) = k4_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) )),
% 2.10/0.67    inference(superposition,[],[f81,f112])).
% 2.10/0.67  fof(f81,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 2.10/0.67    inference(definition_unfolding,[],[f74,f63])).
% 2.10/0.67  fof(f74,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f6])).
% 2.10/0.67  fof(f6,axiom,(
% 2.10/0.67    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.10/0.67  fof(f133,plain,(
% 2.10/0.67    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.10/0.67    inference(forward_demodulation,[],[f130,f127])).
% 2.10/0.67  fof(f127,plain,(
% 2.10/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.10/0.67    inference(resolution,[],[f65,f54])).
% 2.10/0.67  fof(f65,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f30])).
% 2.10/0.67  fof(f30,plain,(
% 2.10/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f9])).
% 2.10/0.67  fof(f9,axiom,(
% 2.10/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.10/0.67  fof(f130,plain,(
% 2.10/0.67    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 2.10/0.67    inference(resolution,[],[f66,f54])).
% 2.10/0.67  fof(f66,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.10/0.67    inference(cnf_transformation,[],[f31])).
% 2.10/0.67  fof(f31,plain,(
% 2.10/0.67    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.67    inference(ennf_transformation,[],[f10])).
% 2.10/0.67  fof(f10,axiom,(
% 2.10/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.10/0.67  fof(f347,plain,(
% 2.10/0.67    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 2.10/0.67    inference(resolution,[],[f128,f83])).
% 2.10/0.67  fof(f128,plain,(
% 2.10/0.67    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)) )),
% 2.10/0.67    inference(resolution,[],[f65,f73])).
% 2.10/0.67  fof(f73,plain,(
% 2.10/0.67    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f48])).
% 2.10/0.67  fof(f545,plain,(
% 2.10/0.67    ( ! [X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(k4_xboole_0(X3,X5),X4)) )),
% 2.10/0.67    inference(superposition,[],[f182,f81])).
% 2.10/0.67  fof(f182,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 2.10/0.67    inference(superposition,[],[f81,f79])).
% 2.10/0.67  fof(f79,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 2.10/0.67    inference(definition_unfolding,[],[f61,f63,f63])).
% 2.10/0.67  fof(f61,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f1])).
% 2.10/0.67  fof(f1,axiom,(
% 2.10/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.10/0.67  fof(f2413,plain,(
% 2.10/0.67    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) | ~spl2_2),
% 2.10/0.67    inference(resolution,[],[f884,f707])).
% 2.10/0.67  fof(f707,plain,(
% 2.10/0.67    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_2),
% 2.10/0.67    inference(superposition,[],[f693,f162])).
% 2.10/0.67  fof(f693,plain,(
% 2.10/0.67    ( ! [X2] : (r1_tarski(k4_xboole_0(sK1,X2),u1_struct_0(sK0))) )),
% 2.10/0.67    inference(superposition,[],[f190,f672])).
% 2.10/0.67  fof(f672,plain,(
% 2.10/0.67    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 2.10/0.67    inference(superposition,[],[f348,f132])).
% 2.10/0.67  fof(f132,plain,(
% 2.10/0.67    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 2.10/0.67    inference(forward_demodulation,[],[f129,f126])).
% 2.10/0.67  fof(f126,plain,(
% 2.10/0.67    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)),
% 2.10/0.67    inference(resolution,[],[f65,f51])).
% 2.10/0.67  fof(f129,plain,(
% 2.10/0.67    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.10/0.67    inference(resolution,[],[f66,f51])).
% 2.10/0.67  fof(f348,plain,(
% 2.10/0.67    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_subset_1(X1,k4_xboole_0(X1,X2))) )),
% 2.10/0.67    inference(resolution,[],[f128,f60])).
% 2.10/0.67  fof(f190,plain,(
% 2.10/0.67    ( ! [X12,X13,X11] : (r1_tarski(k4_xboole_0(k4_xboole_0(X11,X12),X13),X11)) )),
% 2.10/0.67    inference(superposition,[],[f60,f81])).
% 2.10/0.67  fof(f884,plain,(
% 2.10/0.67    ( ! [X8] : (~r1_tarski(X8,u1_struct_0(sK0)) | k5_xboole_0(sK1,k4_xboole_0(X8,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,X8)) )),
% 2.10/0.67    inference(resolution,[],[f320,f51])).
% 2.10/0.67  fof(f320,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) | ~r1_tarski(X2,X0)) )),
% 2.10/0.67    inference(resolution,[],[f82,f73])).
% 2.10/0.67  fof(f82,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.67    inference(definition_unfolding,[],[f77,f63])).
% 2.10/0.67  fof(f77,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f40])).
% 2.10/0.67  fof(f40,plain,(
% 2.10/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.67    inference(flattening,[],[f39])).
% 2.10/0.67  fof(f39,plain,(
% 2.10/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.10/0.67    inference(ennf_transformation,[],[f11])).
% 2.10/0.67  fof(f11,axiom,(
% 2.10/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.10/0.67  fof(f293,plain,(
% 2.10/0.67    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.10/0.67    inference(subsumption_resolution,[],[f291,f50])).
% 2.10/0.67  fof(f291,plain,(
% 2.10/0.67    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.10/0.67    inference(resolution,[],[f56,f51])).
% 2.10/0.67  fof(f56,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f25])).
% 2.10/0.67  fof(f25,plain,(
% 2.10/0.67    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.67    inference(ennf_transformation,[],[f20])).
% 2.10/0.67  fof(f20,axiom,(
% 2.10/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.10/0.67  fof(f59,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f28])).
% 2.10/0.67  fof(f94,plain,(
% 2.10/0.67    spl2_1 | spl2_2),
% 2.10/0.67    inference(avatar_split_clause,[],[f52,f90,f86])).
% 2.10/0.67  fof(f52,plain,(
% 2.10/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.10/0.67    inference(cnf_transformation,[],[f45])).
% 2.10/0.67  fof(f93,plain,(
% 2.10/0.67    ~spl2_1 | ~spl2_2),
% 2.10/0.67    inference(avatar_split_clause,[],[f53,f90,f86])).
% 2.10/0.67  fof(f53,plain,(
% 2.10/0.67    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.10/0.67    inference(cnf_transformation,[],[f45])).
% 2.10/0.67  % SZS output end Proof for theBenchmark
% 2.10/0.67  % (22732)------------------------------
% 2.10/0.67  % (22732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.67  % (22732)Termination reason: Refutation
% 2.10/0.67  
% 2.10/0.67  % (22732)Memory used [KB]: 12537
% 2.10/0.67  % (22732)Time elapsed: 0.219 s
% 2.10/0.67  % (22732)------------------------------
% 2.10/0.67  % (22732)------------------------------
% 2.10/0.68  % (22725)Success in time 0.318 s
%------------------------------------------------------------------------------
