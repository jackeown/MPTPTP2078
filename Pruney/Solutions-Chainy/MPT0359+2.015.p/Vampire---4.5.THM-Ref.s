%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:40 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 280 expanded)
%              Number of leaves         :   32 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :  344 ( 787 expanded)
%              Number of equality atoms :   75 ( 185 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f495,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f90,f91,f97,f127,f131,f140,f151,f335,f452,f456,f475,f489,f493])).

fof(f493,plain,
    ( ~ spl3_14
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | ~ spl3_14
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f474,f488,f286])).

fof(f286,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(global_subsumption,[],[f63,f285])).

fof(f285,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(global_subsumption,[],[f57,f284])).

fof(f284,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X0)
      | ~ r1_tarski(k1_xboole_0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f54,f71])).

fof(f71,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f68,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f48,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f488,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl3_16
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f474,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl3_14
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f489,plain,
    ( ~ spl3_16
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f470,f94,f83,f486])).

fof(f83,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f94,plain,
    ( spl3_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f470,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f85,f95])).

fof(f95,plain,
    ( sK0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f85,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f475,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f458,f94,f78,f472])).

fof(f78,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f458,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f80,f95])).

fof(f80,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f456,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f96,f453])).

fof(f453,plain,
    ( sK0 = sK1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f88,f71])).

fof(f88,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_3
  <=> sK1 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f96,plain,
    ( sK0 != sK1
    | spl3_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f452,plain,
    ( spl3_8
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | spl3_8
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f150,f334,f344])).

fof(f344,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(k5_xboole_0(X10,X9),X9)
      | r1_tarski(X10,X9) ) ),
    inference(superposition,[],[f308,f183])).

fof(f183,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f175,f45])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f175,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f162,f98])).

fof(f98,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f45,f46])).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f162,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f41,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f308,plain,(
    ! [X2,X1] :
      ( r1_tarski(k5_xboole_0(X1,X2),X1)
      | ~ r1_tarski(X2,X1) ) ),
    inference(global_subsumption,[],[f133,f302])).

fof(f302,plain,(
    ! [X2,X1] :
      ( r1_tarski(k5_xboole_0(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f286,f276])).

fof(f276,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(global_subsumption,[],[f133,f272])).

fof(f272,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f72,f111])).

fof(f111,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f56,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f133,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(global_subsumption,[],[f64,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f60,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f334,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl3_12
  <=> r1_tarski(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f150,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_8
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f335,plain,
    ( ~ spl3_7
    | spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f299,f83,f332,f137])).

fof(f137,plain,
    ( spl3_7
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f299,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f84,f276])).

fof(f84,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f151,plain,
    ( ~ spl3_8
    | spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f146,f137,f94,f148])).

fof(f146,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f44,f139])).

fof(f139,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f140,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f134,f124,f137])).

fof(f124,plain,
    ( spl3_6
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f134,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f126,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f126,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f131,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f64,f122])).

fof(f122,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_5
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f127,plain,
    ( spl3_5
    | spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f115,f78,f124,f120])).

fof(f115,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f59,f80])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,
    ( ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f92,f87,f94])).

fof(f92,plain,
    ( sK0 != sK1
    | spl3_3 ),
    inference(superposition,[],[f89,f71])).

fof(f89,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f91,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f70,f87,f83])).

fof(f70,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f39,f68])).

fof(f39,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f90,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f69,f87,f83])).

fof(f69,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f40,f68])).

fof(f40,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:32:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.49  % (25770)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (25779)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.50  % (25774)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.50  % (25787)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.50  % (25790)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (25767)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (25774)Refutation not found, incomplete strategy% (25774)------------------------------
% 0.22/0.51  % (25774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25774)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25774)Memory used [KB]: 10746
% 0.22/0.51  % (25774)Time elapsed: 0.102 s
% 0.22/0.51  % (25774)------------------------------
% 0.22/0.51  % (25774)------------------------------
% 0.22/0.51  % (25768)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (25782)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (25765)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (25765)Refutation not found, incomplete strategy% (25765)------------------------------
% 0.22/0.52  % (25765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25765)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25765)Memory used [KB]: 1663
% 0.22/0.52  % (25765)Time elapsed: 0.107 s
% 0.22/0.52  % (25765)------------------------------
% 0.22/0.52  % (25765)------------------------------
% 0.22/0.52  % (25764)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (25781)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (25769)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (25790)Refutation not found, incomplete strategy% (25790)------------------------------
% 0.22/0.52  % (25790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25783)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (25778)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (25790)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25790)Memory used [KB]: 6268
% 0.22/0.52  % (25790)Time elapsed: 0.106 s
% 0.22/0.52  % (25790)------------------------------
% 0.22/0.52  % (25790)------------------------------
% 0.22/0.52  % (25782)Refutation not found, incomplete strategy% (25782)------------------------------
% 0.22/0.52  % (25782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25782)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25782)Memory used [KB]: 1791
% 0.22/0.52  % (25782)Time elapsed: 0.105 s
% 0.22/0.52  % (25782)------------------------------
% 0.22/0.52  % (25782)------------------------------
% 0.22/0.52  % (25766)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (25793)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (25793)Refutation not found, incomplete strategy% (25793)------------------------------
% 0.22/0.53  % (25793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25793)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25793)Memory used [KB]: 1663
% 0.22/0.53  % (25793)Time elapsed: 0.085 s
% 0.22/0.53  % (25793)------------------------------
% 0.22/0.53  % (25793)------------------------------
% 0.22/0.53  % (25772)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (25780)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (25773)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (25785)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (25789)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (25780)Refutation not found, incomplete strategy% (25780)------------------------------
% 0.22/0.53  % (25780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25780)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25780)Memory used [KB]: 10618
% 0.22/0.53  % (25780)Time elapsed: 0.119 s
% 0.22/0.53  % (25780)------------------------------
% 0.22/0.53  % (25780)------------------------------
% 0.22/0.53  % (25791)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (25786)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (25775)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (25792)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (25777)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (25788)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (25792)Refutation not found, incomplete strategy% (25792)------------------------------
% 0.22/0.54  % (25792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25792)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (25792)Memory used [KB]: 10746
% 0.22/0.54  % (25792)Time elapsed: 0.130 s
% 0.22/0.54  % (25792)------------------------------
% 0.22/0.54  % (25792)------------------------------
% 0.22/0.54  % (25771)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (25784)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (25781)Refutation not found, incomplete strategy% (25781)------------------------------
% 0.22/0.54  % (25781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25781)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (25781)Memory used [KB]: 1791
% 0.22/0.54  % (25781)Time elapsed: 0.128 s
% 0.22/0.54  % (25781)------------------------------
% 0.22/0.54  % (25781)------------------------------
% 0.22/0.54  % (25776)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (25778)Refutation not found, incomplete strategy% (25778)------------------------------
% 0.22/0.55  % (25778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (25778)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (25778)Memory used [KB]: 1791
% 0.22/0.55  % (25778)Time elapsed: 0.143 s
% 0.22/0.55  % (25778)------------------------------
% 0.22/0.55  % (25778)------------------------------
% 0.22/0.55  % (25776)Refutation not found, incomplete strategy% (25776)------------------------------
% 0.22/0.55  % (25776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (25776)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (25776)Memory used [KB]: 10746
% 0.22/0.55  % (25776)Time elapsed: 0.142 s
% 0.22/0.55  % (25776)------------------------------
% 0.22/0.55  % (25776)------------------------------
% 1.56/0.55  % (25787)Refutation found. Thanks to Tanya!
% 1.56/0.55  % SZS status Theorem for theBenchmark
% 1.56/0.55  % SZS output start Proof for theBenchmark
% 1.56/0.55  fof(f495,plain,(
% 1.56/0.55    $false),
% 1.56/0.55    inference(avatar_sat_refutation,[],[f81,f90,f91,f97,f127,f131,f140,f151,f335,f452,f456,f475,f489,f493])).
% 1.56/0.55  fof(f493,plain,(
% 1.56/0.55    ~spl3_14 | spl3_16),
% 1.56/0.55    inference(avatar_contradiction_clause,[],[f490])).
% 1.56/0.55  fof(f490,plain,(
% 1.56/0.55    $false | (~spl3_14 | spl3_16)),
% 1.56/0.55    inference(unit_resulting_resolution,[],[f474,f488,f286])).
% 1.56/0.55  fof(f286,plain,(
% 1.56/0.55    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.56/0.55    inference(global_subsumption,[],[f63,f285])).
% 1.56/0.55  fof(f285,plain,(
% 1.56/0.55    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.56/0.55    inference(global_subsumption,[],[f57,f284])).
% 1.56/0.55  fof(f284,plain,(
% 1.56/0.55    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X0) | ~r1_tarski(k1_xboole_0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.56/0.55    inference(superposition,[],[f54,f71])).
% 1.56/0.55  fof(f71,plain,(
% 1.56/0.55    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.56/0.55    inference(definition_unfolding,[],[f49,f68])).
% 1.56/0.55  fof(f68,plain,(
% 1.56/0.55    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.56/0.55    inference(definition_unfolding,[],[f48,f66])).
% 1.56/0.55  fof(f66,plain,(
% 1.56/0.55    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f12])).
% 1.56/0.55  fof(f12,axiom,(
% 1.56/0.55    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.56/0.55  fof(f48,plain,(
% 1.56/0.55    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.56/0.55    inference(cnf_transformation,[],[f16])).
% 1.56/0.55  fof(f16,axiom,(
% 1.56/0.55    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.56/0.55  fof(f49,plain,(
% 1.56/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.56/0.55    inference(cnf_transformation,[],[f13])).
% 1.56/0.55  fof(f13,axiom,(
% 1.56/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.56/0.55  fof(f54,plain,(
% 1.56/0.55    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.56/0.55    inference(cnf_transformation,[],[f36])).
% 1.56/0.55  fof(f36,plain,(
% 1.56/0.55    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.55    inference(nnf_transformation,[],[f22])).
% 1.56/0.55  fof(f22,plain,(
% 1.56/0.55    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.55    inference(ennf_transformation,[],[f17])).
% 1.56/0.55  fof(f17,axiom,(
% 1.56/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 1.56/0.55  fof(f57,plain,(
% 1.56/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f6])).
% 1.56/0.55  fof(f6,axiom,(
% 1.56/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.56/0.55  fof(f63,plain,(
% 1.56/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.56/0.55    inference(cnf_transformation,[],[f18])).
% 1.56/0.55  fof(f18,axiom,(
% 1.56/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.56/0.55  fof(f488,plain,(
% 1.56/0.55    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl3_16),
% 1.56/0.55    inference(avatar_component_clause,[],[f486])).
% 1.56/0.55  fof(f486,plain,(
% 1.56/0.55    spl3_16 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.56/0.55  fof(f474,plain,(
% 1.56/0.55    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_14),
% 1.56/0.55    inference(avatar_component_clause,[],[f472])).
% 1.56/0.55  fof(f472,plain,(
% 1.56/0.55    spl3_14 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.56/0.55  fof(f489,plain,(
% 1.56/0.55    ~spl3_16 | spl3_2 | ~spl3_4),
% 1.56/0.55    inference(avatar_split_clause,[],[f470,f94,f83,f486])).
% 1.56/0.55  fof(f83,plain,(
% 1.56/0.55    spl3_2 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.56/0.55  fof(f94,plain,(
% 1.56/0.55    spl3_4 <=> sK0 = sK1),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.56/0.55  fof(f470,plain,(
% 1.56/0.55    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl3_2 | ~spl3_4)),
% 1.56/0.55    inference(forward_demodulation,[],[f85,f95])).
% 1.56/0.55  fof(f95,plain,(
% 1.56/0.55    sK0 = sK1 | ~spl3_4),
% 1.56/0.55    inference(avatar_component_clause,[],[f94])).
% 1.56/0.55  fof(f85,plain,(
% 1.56/0.55    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl3_2),
% 1.56/0.55    inference(avatar_component_clause,[],[f83])).
% 1.56/0.55  fof(f475,plain,(
% 1.56/0.55    spl3_14 | ~spl3_1 | ~spl3_4),
% 1.56/0.55    inference(avatar_split_clause,[],[f458,f94,f78,f472])).
% 1.56/0.55  fof(f78,plain,(
% 1.56/0.55    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.56/0.55  fof(f458,plain,(
% 1.56/0.55    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | (~spl3_1 | ~spl3_4)),
% 1.56/0.55    inference(superposition,[],[f80,f95])).
% 1.56/0.55  fof(f80,plain,(
% 1.56/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.56/0.55    inference(avatar_component_clause,[],[f78])).
% 1.56/0.55  fof(f456,plain,(
% 1.56/0.55    ~spl3_3 | spl3_4),
% 1.56/0.55    inference(avatar_contradiction_clause,[],[f454])).
% 1.56/0.55  fof(f454,plain,(
% 1.56/0.55    $false | (~spl3_3 | spl3_4)),
% 1.56/0.55    inference(subsumption_resolution,[],[f96,f453])).
% 1.56/0.55  fof(f453,plain,(
% 1.56/0.55    sK0 = sK1 | ~spl3_3),
% 1.56/0.55    inference(forward_demodulation,[],[f88,f71])).
% 1.56/0.55  fof(f88,plain,(
% 1.56/0.55    sK1 = k3_subset_1(sK0,k1_xboole_0) | ~spl3_3),
% 1.56/0.55    inference(avatar_component_clause,[],[f87])).
% 1.56/0.55  fof(f87,plain,(
% 1.56/0.55    spl3_3 <=> sK1 = k3_subset_1(sK0,k1_xboole_0)),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.56/0.55  fof(f96,plain,(
% 1.56/0.55    sK0 != sK1 | spl3_4),
% 1.56/0.55    inference(avatar_component_clause,[],[f94])).
% 1.56/0.55  fof(f452,plain,(
% 1.56/0.55    spl3_8 | ~spl3_12),
% 1.56/0.55    inference(avatar_contradiction_clause,[],[f436])).
% 1.56/0.55  fof(f436,plain,(
% 1.56/0.55    $false | (spl3_8 | ~spl3_12)),
% 1.56/0.55    inference(unit_resulting_resolution,[],[f150,f334,f344])).
% 1.56/0.55  fof(f344,plain,(
% 1.56/0.55    ( ! [X10,X9] : (~r1_tarski(k5_xboole_0(X10,X9),X9) | r1_tarski(X10,X9)) )),
% 1.56/0.55    inference(superposition,[],[f308,f183])).
% 1.56/0.55  fof(f183,plain,(
% 1.56/0.55    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.56/0.55    inference(superposition,[],[f175,f45])).
% 1.56/0.55  fof(f45,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f2])).
% 1.56/0.55  fof(f2,axiom,(
% 1.56/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.56/0.55  fof(f175,plain,(
% 1.56/0.55    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 1.56/0.55    inference(forward_demodulation,[],[f162,f98])).
% 1.56/0.55  fof(f98,plain,(
% 1.56/0.55    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.56/0.55    inference(superposition,[],[f45,f46])).
% 1.56/0.55  fof(f46,plain,(
% 1.56/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.56/0.55    inference(cnf_transformation,[],[f7])).
% 1.56/0.55  fof(f7,axiom,(
% 1.56/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.56/0.55  fof(f162,plain,(
% 1.56/0.55    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 1.56/0.55    inference(superposition,[],[f41,f47])).
% 1.56/0.55  fof(f47,plain,(
% 1.56/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f9])).
% 1.56/0.55  fof(f9,axiom,(
% 1.56/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.56/0.55  fof(f41,plain,(
% 1.56/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.56/0.55    inference(cnf_transformation,[],[f8])).
% 1.56/0.55  fof(f8,axiom,(
% 1.56/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.56/0.55  fof(f308,plain,(
% 1.56/0.55    ( ! [X2,X1] : (r1_tarski(k5_xboole_0(X1,X2),X1) | ~r1_tarski(X2,X1)) )),
% 1.56/0.55    inference(global_subsumption,[],[f133,f302])).
% 1.56/0.55  fof(f302,plain,(
% 1.56/0.55    ( ! [X2,X1] : (r1_tarski(k5_xboole_0(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~r1_tarski(X2,X1)) )),
% 1.56/0.55    inference(superposition,[],[f286,f276])).
% 1.56/0.55  fof(f276,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.56/0.55    inference(global_subsumption,[],[f133,f272])).
% 1.56/0.55  fof(f272,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 1.56/0.55    inference(superposition,[],[f72,f111])).
% 1.56/0.55  fof(f111,plain,(
% 1.56/0.55    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 1.56/0.55    inference(superposition,[],[f56,f67])).
% 1.56/0.55  fof(f67,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f1])).
% 1.56/0.55  fof(f1,axiom,(
% 1.56/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.56/0.55  fof(f56,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f23])).
% 1.56/0.55  fof(f23,plain,(
% 1.56/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.56/0.55    inference(ennf_transformation,[],[f5])).
% 1.56/0.55  fof(f5,axiom,(
% 1.56/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.56/0.55  fof(f72,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.56/0.55    inference(definition_unfolding,[],[f58,f65])).
% 1.56/0.55  fof(f65,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.56/0.55    inference(cnf_transformation,[],[f4])).
% 1.56/0.55  fof(f4,axiom,(
% 1.56/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.56/0.55  fof(f58,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.56/0.55    inference(cnf_transformation,[],[f24])).
% 1.56/0.55  fof(f24,plain,(
% 1.56/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.55    inference(ennf_transformation,[],[f14])).
% 1.56/0.55  fof(f14,axiom,(
% 1.56/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.56/0.55  fof(f133,plain,(
% 1.56/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.56/0.55    inference(global_subsumption,[],[f64,f132])).
% 1.56/0.55  fof(f132,plain,(
% 1.56/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.56/0.55    inference(resolution,[],[f60,f75])).
% 1.56/0.55  fof(f75,plain,(
% 1.56/0.55    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.56/0.55    inference(equality_resolution,[],[f51])).
% 1.56/0.55  fof(f51,plain,(
% 1.56/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.56/0.55    inference(cnf_transformation,[],[f35])).
% 1.56/0.55  fof(f35,plain,(
% 1.56/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.56/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 1.56/0.55  fof(f34,plain,(
% 1.56/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.56/0.55    introduced(choice_axiom,[])).
% 1.56/0.55  fof(f33,plain,(
% 1.56/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.56/0.55    inference(rectify,[],[f32])).
% 1.56/0.55  fof(f32,plain,(
% 1.56/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.56/0.55    inference(nnf_transformation,[],[f10])).
% 1.56/0.55  fof(f10,axiom,(
% 1.56/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.56/0.55  fof(f60,plain,(
% 1.56/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f37])).
% 1.56/0.55  fof(f37,plain,(
% 1.56/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.56/0.55    inference(nnf_transformation,[],[f25])).
% 1.56/0.55  fof(f25,plain,(
% 1.56/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.56/0.55    inference(ennf_transformation,[],[f11])).
% 1.56/0.55  fof(f11,axiom,(
% 1.56/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.56/0.55  fof(f64,plain,(
% 1.56/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.56/0.55    inference(cnf_transformation,[],[f15])).
% 1.56/0.55  fof(f15,axiom,(
% 1.56/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.56/0.55  fof(f334,plain,(
% 1.56/0.55    r1_tarski(k5_xboole_0(sK0,sK1),sK1) | ~spl3_12),
% 1.56/0.55    inference(avatar_component_clause,[],[f332])).
% 1.56/0.55  fof(f332,plain,(
% 1.56/0.55    spl3_12 <=> r1_tarski(k5_xboole_0(sK0,sK1),sK1)),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.56/0.55  fof(f150,plain,(
% 1.56/0.55    ~r1_tarski(sK0,sK1) | spl3_8),
% 1.56/0.55    inference(avatar_component_clause,[],[f148])).
% 1.56/0.55  fof(f148,plain,(
% 1.56/0.55    spl3_8 <=> r1_tarski(sK0,sK1)),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.56/0.55  fof(f335,plain,(
% 1.56/0.55    ~spl3_7 | spl3_12 | ~spl3_2),
% 1.56/0.55    inference(avatar_split_clause,[],[f299,f83,f332,f137])).
% 1.56/0.55  fof(f137,plain,(
% 1.56/0.55    spl3_7 <=> r1_tarski(sK1,sK0)),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.56/0.55  fof(f299,plain,(
% 1.56/0.55    r1_tarski(k5_xboole_0(sK0,sK1),sK1) | ~r1_tarski(sK1,sK0) | ~spl3_2),
% 1.56/0.55    inference(superposition,[],[f84,f276])).
% 1.56/0.55  fof(f84,plain,(
% 1.56/0.55    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_2),
% 1.56/0.55    inference(avatar_component_clause,[],[f83])).
% 1.56/0.55  fof(f151,plain,(
% 1.56/0.55    ~spl3_8 | spl3_4 | ~spl3_7),
% 1.56/0.55    inference(avatar_split_clause,[],[f146,f137,f94,f148])).
% 1.56/0.55  fof(f146,plain,(
% 1.56/0.55    sK0 = sK1 | ~r1_tarski(sK0,sK1) | ~spl3_7),
% 1.56/0.55    inference(resolution,[],[f44,f139])).
% 1.56/0.55  fof(f139,plain,(
% 1.56/0.55    r1_tarski(sK1,sK0) | ~spl3_7),
% 1.56/0.55    inference(avatar_component_clause,[],[f137])).
% 1.56/0.55  fof(f44,plain,(
% 1.56/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f31])).
% 1.56/0.55  fof(f31,plain,(
% 1.56/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.55    inference(flattening,[],[f30])).
% 1.56/0.55  fof(f30,plain,(
% 1.56/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.55    inference(nnf_transformation,[],[f3])).
% 1.56/0.55  fof(f3,axiom,(
% 1.56/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.55  fof(f140,plain,(
% 1.56/0.55    spl3_7 | ~spl3_6),
% 1.56/0.55    inference(avatar_split_clause,[],[f134,f124,f137])).
% 1.56/0.55  fof(f124,plain,(
% 1.56/0.55    spl3_6 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.56/0.55  fof(f134,plain,(
% 1.56/0.55    r1_tarski(sK1,sK0) | ~spl3_6),
% 1.56/0.55    inference(resolution,[],[f126,f76])).
% 1.56/0.55  fof(f76,plain,(
% 1.56/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.56/0.55    inference(equality_resolution,[],[f50])).
% 1.56/0.55  fof(f50,plain,(
% 1.56/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.56/0.55    inference(cnf_transformation,[],[f35])).
% 1.56/0.55  fof(f126,plain,(
% 1.56/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_6),
% 1.56/0.55    inference(avatar_component_clause,[],[f124])).
% 1.56/0.55  fof(f131,plain,(
% 1.56/0.55    ~spl3_5),
% 1.56/0.55    inference(avatar_contradiction_clause,[],[f128])).
% 1.56/0.55  fof(f128,plain,(
% 1.56/0.55    $false | ~spl3_5),
% 1.56/0.55    inference(unit_resulting_resolution,[],[f64,f122])).
% 1.56/0.55  fof(f122,plain,(
% 1.56/0.55    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_5),
% 1.56/0.55    inference(avatar_component_clause,[],[f120])).
% 1.56/0.55  fof(f120,plain,(
% 1.56/0.55    spl3_5 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.56/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.56/0.55  fof(f127,plain,(
% 1.56/0.55    spl3_5 | spl3_6 | ~spl3_1),
% 1.56/0.55    inference(avatar_split_clause,[],[f115,f78,f124,f120])).
% 1.56/0.55  fof(f115,plain,(
% 1.56/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.56/0.55    inference(resolution,[],[f59,f80])).
% 1.56/0.55  fof(f59,plain,(
% 1.56/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f37])).
% 1.56/0.55  fof(f97,plain,(
% 1.56/0.55    ~spl3_4 | spl3_3),
% 1.56/0.55    inference(avatar_split_clause,[],[f92,f87,f94])).
% 1.56/0.55  fof(f92,plain,(
% 1.56/0.55    sK0 != sK1 | spl3_3),
% 1.56/0.55    inference(superposition,[],[f89,f71])).
% 1.56/0.55  fof(f89,plain,(
% 1.56/0.55    sK1 != k3_subset_1(sK0,k1_xboole_0) | spl3_3),
% 1.56/0.55    inference(avatar_component_clause,[],[f87])).
% 1.56/0.55  fof(f91,plain,(
% 1.56/0.55    spl3_2 | spl3_3),
% 1.56/0.55    inference(avatar_split_clause,[],[f70,f87,f83])).
% 1.56/0.55  fof(f70,plain,(
% 1.56/0.55    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.56/0.55    inference(definition_unfolding,[],[f39,f68])).
% 1.56/0.55  fof(f39,plain,(
% 1.56/0.55    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.56/0.55    inference(cnf_transformation,[],[f29])).
% 1.56/0.55  fof(f29,plain,(
% 1.56/0.55    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.56/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 1.56/0.55  fof(f28,plain,(
% 1.56/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.56/0.55    introduced(choice_axiom,[])).
% 1.56/0.55  fof(f27,plain,(
% 1.56/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.55    inference(flattening,[],[f26])).
% 1.56/0.55  fof(f26,plain,(
% 1.56/0.55    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.55    inference(nnf_transformation,[],[f21])).
% 1.56/0.55  fof(f21,plain,(
% 1.56/0.55    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.55    inference(ennf_transformation,[],[f20])).
% 1.56/0.55  fof(f20,negated_conjecture,(
% 1.56/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.56/0.55    inference(negated_conjecture,[],[f19])).
% 1.56/0.55  fof(f19,conjecture,(
% 1.56/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.56/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 1.56/0.55  fof(f90,plain,(
% 1.56/0.55    ~spl3_2 | ~spl3_3),
% 1.56/0.55    inference(avatar_split_clause,[],[f69,f87,f83])).
% 1.56/0.55  fof(f69,plain,(
% 1.56/0.55    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.56/0.55    inference(definition_unfolding,[],[f40,f68])).
% 1.56/0.55  fof(f40,plain,(
% 1.56/0.55    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.56/0.55    inference(cnf_transformation,[],[f29])).
% 1.56/0.55  fof(f81,plain,(
% 1.56/0.55    spl3_1),
% 1.56/0.55    inference(avatar_split_clause,[],[f38,f78])).
% 1.56/0.55  fof(f38,plain,(
% 1.56/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.56/0.55    inference(cnf_transformation,[],[f29])).
% 1.56/0.55  % SZS output end Proof for theBenchmark
% 1.56/0.55  % (25787)------------------------------
% 1.56/0.55  % (25787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.55  % (25787)Termination reason: Refutation
% 1.56/0.55  
% 1.56/0.55  % (25787)Memory used [KB]: 11129
% 1.56/0.55  % (25787)Time elapsed: 0.149 s
% 1.56/0.55  % (25787)------------------------------
% 1.56/0.55  % (25787)------------------------------
% 1.56/0.56  % (25763)Success in time 0.193 s
%------------------------------------------------------------------------------
