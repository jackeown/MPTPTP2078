%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 398 expanded)
%              Number of leaves         :   22 ( 119 expanded)
%              Depth                    :   20
%              Number of atoms          :  365 (2123 expanded)
%              Number of equality atoms :   69 ( 537 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f77,f137,f172,f203,f208,f211,f290,f294,f306])).

fof(f306,plain,
    ( spl2_2
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | spl2_2
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f302,f75])).

fof(f75,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_2
  <=> sK1 = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f302,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f263,f283])).

fof(f283,plain,
    ( sK1 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl2_9
  <=> sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f263,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f261,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( sK1 != k2_tops_1(sK0,sK1)
      | ~ v3_tops_1(sK1,sK0) )
    & ( sK1 = k2_tops_1(sK0,sK1)
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != X1
          | ~ v3_tops_1(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = X1
          | v3_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( sK1 != k2_tops_1(sK0,sK1)
        | ~ v3_tops_1(sK1,sK0) )
      & ( sK1 = k2_tops_1(sK0,sK1)
        | v3_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

fof(f261,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(superposition,[],[f253,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f253,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f252,f132])).

fof(f132,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_5
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f252,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f251,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f251,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f239,f43])).

fof(f239,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f48,f121])).

fof(f121,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f120,f42])).

fof(f120,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f119,f44])).

fof(f44,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f43])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f294,plain,
    ( spl2_9
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f293,f277,f205,f130,f281])).

fof(f205,plain,
    ( spl2_7
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f277,plain,
    ( spl2_8
  <=> r1_tarski(k4_xboole_0(sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f293,plain,
    ( sK1 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f291,f267])).

fof(f267,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK1,k1_xboole_0))
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f207,f263])).

fof(f207,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f205])).

fof(f291,plain,
    ( sK1 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ r1_tarski(sK1,k4_xboole_0(sK1,k1_xboole_0))
    | ~ spl2_8 ),
    inference(resolution,[],[f278,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f278,plain,
    ( r1_tarski(k4_xboole_0(sK1,k1_xboole_0),sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f277])).

fof(f290,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl2_8 ),
    inference(subsumption_resolution,[],[f288,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f288,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl2_8 ),
    inference(resolution,[],[f287,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X1,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f57,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f287,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k1_xboole_0),sK1)
    | spl2_8 ),
    inference(subsumption_resolution,[],[f286,f47])).

fof(f286,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k1_xboole_0),sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl2_8 ),
    inference(superposition,[],[f279,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f279,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k1_xboole_0),sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f277])).

fof(f211,plain,
    ( spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f210,f134,f69])).

fof(f69,plain,
    ( spl2_1
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f134,plain,
    ( spl2_6
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f210,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f195,f42])).

fof(f195,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f193,f44])).

fof(f193,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | v3_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

fof(f208,plain,
    ( spl2_7
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f173,f134,f205])).

fof(f173,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f158,f42])).

fof(f158,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f203,plain,
    ( spl2_6
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f202,f69,f134])).

fof(f202,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f111,f42])).

fof(f111,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f51,f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(f172,plain,
    ( spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f171,f73,f134])).

fof(f171,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f170,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f170,plain,
    ( ~ r1_tarski(sK1,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f169,f74])).

fof(f74,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f169,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f162,f42])).

fof(f162,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f137,plain,
    ( spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f128,f134,f130])).

fof(f128,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f127,f42])).

fof(f127,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f77,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f45,f73,f69])).

fof(f45,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f46,f73,f69])).

fof(f46,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (23199)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (23215)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.48  % (23209)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (23209)Refutation not found, incomplete strategy% (23209)------------------------------
% 0.20/0.48  % (23209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23209)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (23209)Memory used [KB]: 6140
% 0.20/0.48  % (23209)Time elapsed: 0.078 s
% 0.20/0.48  % (23209)------------------------------
% 0.20/0.48  % (23209)------------------------------
% 0.20/0.49  % (23200)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (23216)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (23199)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (23208)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (23200)Refutation not found, incomplete strategy% (23200)------------------------------
% 0.20/0.49  % (23200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23200)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23200)Memory used [KB]: 6140
% 0.20/0.49  % (23200)Time elapsed: 0.093 s
% 0.20/0.49  % (23200)------------------------------
% 0.20/0.49  % (23200)------------------------------
% 0.20/0.49  % (23198)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (23217)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f309,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f76,f77,f137,f172,f203,f208,f211,f290,f294,f306])).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    spl2_2 | ~spl2_5 | ~spl2_9),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f305])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    $false | (spl2_2 | ~spl2_5 | ~spl2_9)),
% 0.20/0.50    inference(subsumption_resolution,[],[f302,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    sK1 != k2_tops_1(sK0,sK1) | spl2_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    spl2_2 <=> sK1 = k2_tops_1(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    sK1 = k2_tops_1(sK0,sK1) | (~spl2_5 | ~spl2_9)),
% 0.20/0.50    inference(backward_demodulation,[],[f263,f283])).
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    sK1 = k4_xboole_0(sK1,k1_xboole_0) | ~spl2_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f281])).
% 0.20/0.50  fof(f281,plain,(
% 0.20/0.50    spl2_9 <=> sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) | ~spl2_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f261,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f14])).
% 0.20/0.50  fof(f14,conjecture,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.20/0.50    inference(superposition,[],[f253,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | ~spl2_5),
% 0.20/0.50    inference(forward_demodulation,[],[f252,f132])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f130])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    spl2_5 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.50  fof(f252,plain,(
% 0.20/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f251,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f239,f43])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(superposition,[],[f48,f121])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f120,f42])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f119,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    v4_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(resolution,[],[f49,f43])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    spl2_9 | ~spl2_5 | ~spl2_7 | ~spl2_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f293,f277,f205,f130,f281])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    spl2_7 <=> r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.50  fof(f277,plain,(
% 0.20/0.50    spl2_8 <=> r1_tarski(k4_xboole_0(sK1,k1_xboole_0),sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    sK1 = k4_xboole_0(sK1,k1_xboole_0) | (~spl2_5 | ~spl2_7 | ~spl2_8)),
% 0.20/0.50    inference(subsumption_resolution,[],[f291,f267])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    r1_tarski(sK1,k4_xboole_0(sK1,k1_xboole_0)) | (~spl2_5 | ~spl2_7)),
% 0.20/0.50    inference(backward_demodulation,[],[f207,f263])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~spl2_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f205])).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    sK1 = k4_xboole_0(sK1,k1_xboole_0) | ~r1_tarski(sK1,k4_xboole_0(sK1,k1_xboole_0)) | ~spl2_8),
% 0.20/0.50    inference(resolution,[],[f278,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    r1_tarski(k4_xboole_0(sK1,k1_xboole_0),sK1) | ~spl2_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f277])).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    spl2_8),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f289])).
% 0.20/0.50  fof(f289,plain,(
% 0.20/0.50    $false | spl2_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f288,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.50  fof(f288,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl2_8),
% 0.20/0.50    inference(resolution,[],[f287,f95])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X1,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(resolution,[],[f57,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    ~r1_tarski(k3_subset_1(sK1,k1_xboole_0),sK1) | spl2_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f286,f47])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    ~r1_tarski(k3_subset_1(sK1,k1_xboole_0),sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl2_8),
% 0.20/0.50    inference(superposition,[],[f279,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.50  fof(f279,plain,(
% 0.20/0.50    ~r1_tarski(k4_xboole_0(sK1,k1_xboole_0),sK1) | spl2_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f277])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    spl2_1 | ~spl2_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f210,f134,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    spl2_1 <=> v3_tops_1(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    spl2_6 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    ~v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f195,f42])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    ~v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f193,f44])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    ~v4_pre_topc(sK1,sK0) | ~v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(resolution,[],[f52,f43])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | v3_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    spl2_7 | ~spl2_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f173,f134,f205])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    ~v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f158,f42])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    ~v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(resolution,[],[f55,f43])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | r1_tarski(X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    spl2_6 | ~spl2_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f202,f69,f134])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    ~v3_tops_1(sK1,sK0) | v2_tops_1(sK1,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f111,f42])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    ~v3_tops_1(sK1,sK0) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(resolution,[],[f51,f43])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    spl2_6 | ~spl2_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f171,f73,f134])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    v2_tops_1(sK1,sK0) | ~spl2_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f170,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    ~r1_tarski(sK1,sK1) | v2_tops_1(sK1,sK0) | ~spl2_2),
% 0.20/0.50    inference(forward_demodulation,[],[f169,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    sK1 = k2_tops_1(sK0,sK1) | ~spl2_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f73])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f162,f42])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(resolution,[],[f56,f43])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    spl2_5 | ~spl2_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f128,f134,f130])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f127,f42])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(resolution,[],[f53,f43])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl2_1 | spl2_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f45,f73,f69])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ~spl2_1 | ~spl2_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f46,f73,f69])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (23199)------------------------------
% 0.20/0.50  % (23199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23199)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (23199)Memory used [KB]: 6268
% 0.20/0.50  % (23199)Time elapsed: 0.074 s
% 0.20/0.50  % (23199)------------------------------
% 0.20/0.50  % (23199)------------------------------
% 0.20/0.50  % (23207)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (23191)Success in time 0.148 s
%------------------------------------------------------------------------------
