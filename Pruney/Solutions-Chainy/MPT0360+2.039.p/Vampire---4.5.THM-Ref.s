%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:53 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 451 expanded)
%              Number of leaves         :   20 ( 128 expanded)
%              Depth                    :   15
%              Number of atoms          :  314 (1286 expanded)
%              Number of equality atoms :   55 ( 308 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f629,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f177,f187,f407,f549,f558,f568,f615,f628])).

fof(f628,plain,
    ( ~ spl5_6
    | ~ spl5_31
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_31
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f623,f41])).

fof(f41,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f623,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_6
    | ~ spl5_31
    | ~ spl5_32 ),
    inference(backward_demodulation,[],[f175,f619])).

fof(f619,plain,
    ( k1_xboole_0 = k3_subset_1(sK1,sK1)
    | ~ spl5_31
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f617,f561])).

fof(f561,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f560])).

fof(f560,plain,
    ( spl5_31
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f617,plain,
    ( k1_xboole_0 = k3_subset_1(sK1,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl5_32 ),
    inference(superposition,[],[f51,f566])).

fof(f566,plain,
    ( sK1 = k3_subset_1(sK1,k1_xboole_0)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f564])).

fof(f564,plain,
    ( spl5_32
  <=> sK1 = k3_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f175,plain,
    ( sK1 = k3_subset_1(sK1,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl5_6
  <=> sK1 = k3_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f615,plain,
    ( ~ spl5_7
    | spl5_31 ),
    inference(avatar_contradiction_clause,[],[f614])).

fof(f614,plain,
    ( $false
    | ~ spl5_7
    | spl5_31 ),
    inference(subsumption_resolution,[],[f596,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f596,plain,
    ( ! [X9] : ~ r1_tarski(k1_xboole_0,k5_xboole_0(X9,k3_xboole_0(X9,sK2)))
    | ~ spl5_7
    | spl5_31 ),
    inference(resolution,[],[f580,f95])).

fof(f95,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(X2,sK1)
      | ~ r1_tarski(X2,k5_xboole_0(X1,k3_xboole_0(X1,sK2))) ) ),
    inference(superposition,[],[f67,f86])).

fof(f86,plain,(
    ! [X0] : sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2)))) ),
    inference(resolution,[],[f72,f39])).

fof(f39,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X0 ) ),
    inference(resolution,[],[f67,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f52,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f43])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f580,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ spl5_7
    | spl5_31 ),
    inference(subsumption_resolution,[],[f576,f42])).

fof(f576,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ r1_xboole_0(k1_xboole_0,X0) )
    | ~ spl5_7
    | spl5_31 ),
    inference(resolution,[],[f575,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f575,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_7
    | spl5_31 ),
    inference(subsumption_resolution,[],[f574,f181])).

fof(f181,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl5_7
  <=> v1_xboole_0(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f574,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_31 ),
    inference(resolution,[],[f562,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f562,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f560])).

fof(f568,plain,
    ( ~ spl5_31
    | spl5_32 ),
    inference(avatar_split_clause,[],[f534,f564,f560])).

fof(f534,plain,
    ( sK1 = k3_subset_1(sK1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f506,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f506,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f87,f192])).

fof(f192,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f73,f42])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = X0 ) ),
    inference(resolution,[],[f68,f66])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f63,f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f87,plain,(
    ! [X1] : sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(sK0,sK2))))) ),
    inference(resolution,[],[f72,f40])).

fof(f40,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f558,plain,
    ( ~ spl5_6
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f557])).

fof(f557,plain,
    ( $false
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f556,f41])).

fof(f556,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_6
    | spl5_7 ),
    inference(forward_demodulation,[],[f175,f546])).

fof(f546,plain,
    ( k1_xboole_0 = k3_subset_1(sK1,sK1)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f544,f327])).

fof(f327,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl5_7 ),
    inference(resolution,[],[f317,f42])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | spl5_7 ),
    inference(resolution,[],[f189,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f189,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_zfmisc_1(sK1))
        | m1_subset_1(X1,k1_zfmisc_1(sK1)) )
    | spl5_7 ),
    inference(resolution,[],[f182,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f182,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f180])).

fof(f544,plain,
    ( k1_xboole_0 = k3_subset_1(sK1,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl5_7 ),
    inference(superposition,[],[f51,f540])).

fof(f540,plain,
    ( sK1 = k3_subset_1(sK1,k1_xboole_0)
    | spl5_7 ),
    inference(subsumption_resolution,[],[f534,f327])).

fof(f549,plain,
    ( spl5_5
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | spl5_5
    | spl5_7 ),
    inference(subsumption_resolution,[],[f547,f327])).

fof(f547,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl5_5
    | spl5_7 ),
    inference(subsumption_resolution,[],[f545,f171])).

fof(f171,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f545,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl5_7 ),
    inference(superposition,[],[f49,f540])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f407,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl5_8 ),
    inference(subsumption_resolution,[],[f402,f150])).

fof(f150,plain,(
    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f149])).

fof(f149,plain,
    ( sK1 != sK1
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f65,f111])).

fof(f111,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK2))) ),
    inference(resolution,[],[f92,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(X0,sK2))) ) ),
    inference(superposition,[],[f86,f64])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f43])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f402,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | spl5_8 ),
    inference(resolution,[],[f390,f40])).

fof(f390,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_xboole_0(sK1,X0) )
    | spl5_8 ),
    inference(resolution,[],[f186,f48])).

fof(f186,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f187,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | spl5_5 ),
    inference(avatar_split_clause,[],[f178,f169,f184,f180])).

fof(f178,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_5 ),
    inference(resolution,[],[f171,f47])).

fof(f177,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f164,f173,f169])).

fof(f164,plain,
    ( sK1 = k3_subset_1(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f64,f146])).

fof(f146,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f87,f111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:21:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (9229)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (9237)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (9226)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (9229)Refutation not found, incomplete strategy% (9229)------------------------------
% 0.21/0.51  % (9229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9229)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9229)Memory used [KB]: 10618
% 0.21/0.51  % (9229)Time elapsed: 0.061 s
% 0.21/0.51  % (9229)------------------------------
% 0.21/0.51  % (9229)------------------------------
% 0.21/0.52  % (9219)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (9234)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (9218)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.52  % (9227)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.22/0.53  % (9235)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.22/0.53  % (9216)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.53  % (9221)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.22/0.53  % (9238)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.22/0.53  % (9221)Refutation not found, incomplete strategy% (9221)------------------------------
% 1.22/0.53  % (9221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (9221)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (9221)Memory used [KB]: 10618
% 1.22/0.53  % (9221)Time elapsed: 0.096 s
% 1.22/0.53  % (9221)------------------------------
% 1.22/0.53  % (9221)------------------------------
% 1.22/0.53  % (9213)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.54  % (9217)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.54  % (9214)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.54  % (9232)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.22/0.54  % (9234)Refutation not found, incomplete strategy% (9234)------------------------------
% 1.22/0.54  % (9234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.54  % (9234)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.54  
% 1.22/0.54  % (9234)Memory used [KB]: 10746
% 1.22/0.54  % (9234)Time elapsed: 0.122 s
% 1.22/0.54  % (9234)------------------------------
% 1.22/0.54  % (9234)------------------------------
% 1.40/0.55  % (9212)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.55  % (9236)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.55  % (9215)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.40/0.55  % (9212)Refutation not found, incomplete strategy% (9212)------------------------------
% 1.40/0.55  % (9212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (9225)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.55  % (9222)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.55  % (9224)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.55  % (9230)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.55  % (9214)Refutation not found, incomplete strategy% (9214)------------------------------
% 1.40/0.55  % (9214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (9214)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (9214)Memory used [KB]: 10746
% 1.40/0.55  % (9214)Time elapsed: 0.130 s
% 1.40/0.55  % (9214)------------------------------
% 1.40/0.55  % (9214)------------------------------
% 1.40/0.55  % (9222)Refutation not found, incomplete strategy% (9222)------------------------------
% 1.40/0.55  % (9222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (9220)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.55  % (9212)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (9212)Memory used [KB]: 1663
% 1.40/0.55  % (9212)Time elapsed: 0.136 s
% 1.40/0.55  % (9212)------------------------------
% 1.40/0.55  % (9212)------------------------------
% 1.40/0.55  % (9222)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (9222)Memory used [KB]: 10618
% 1.40/0.55  % (9222)Time elapsed: 0.137 s
% 1.40/0.55  % (9222)------------------------------
% 1.40/0.55  % (9222)------------------------------
% 1.40/0.55  % (9241)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.55  % (9228)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.55  % (9240)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.56  % (9220)Refutation not found, incomplete strategy% (9220)------------------------------
% 1.40/0.56  % (9220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (9239)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.56  % (9220)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (9220)Memory used [KB]: 10746
% 1.40/0.56  % (9233)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.56  % (9220)Time elapsed: 0.150 s
% 1.40/0.56  % (9220)------------------------------
% 1.40/0.56  % (9220)------------------------------
% 1.40/0.56  % (9231)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.57  % (9223)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.58  % (9215)Refutation found. Thanks to Tanya!
% 1.40/0.58  % SZS status Theorem for theBenchmark
% 1.40/0.58  % SZS output start Proof for theBenchmark
% 1.40/0.58  fof(f629,plain,(
% 1.40/0.58    $false),
% 1.40/0.58    inference(avatar_sat_refutation,[],[f177,f187,f407,f549,f558,f568,f615,f628])).
% 1.40/0.58  fof(f628,plain,(
% 1.40/0.58    ~spl5_6 | ~spl5_31 | ~spl5_32),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f627])).
% 1.40/0.58  fof(f627,plain,(
% 1.40/0.58    $false | (~spl5_6 | ~spl5_31 | ~spl5_32)),
% 1.40/0.58    inference(subsumption_resolution,[],[f623,f41])).
% 1.40/0.58  fof(f41,plain,(
% 1.40/0.58    k1_xboole_0 != sK1),
% 1.40/0.58    inference(cnf_transformation,[],[f27])).
% 1.40/0.58  fof(f27,plain,(
% 1.40/0.58    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.40/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).
% 1.40/0.58  fof(f26,plain,(
% 1.40/0.58    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.40/0.58    introduced(choice_axiom,[])).
% 1.40/0.58  fof(f16,plain,(
% 1.40/0.58    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.40/0.58    inference(flattening,[],[f15])).
% 1.40/0.58  fof(f15,plain,(
% 1.40/0.58    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.40/0.58    inference(ennf_transformation,[],[f14])).
% 1.40/0.58  fof(f14,negated_conjecture,(
% 1.40/0.58    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.40/0.58    inference(negated_conjecture,[],[f13])).
% 1.40/0.58  fof(f13,conjecture,(
% 1.40/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 1.40/0.58  fof(f623,plain,(
% 1.40/0.58    k1_xboole_0 = sK1 | (~spl5_6 | ~spl5_31 | ~spl5_32)),
% 1.40/0.58    inference(backward_demodulation,[],[f175,f619])).
% 1.40/0.58  fof(f619,plain,(
% 1.40/0.58    k1_xboole_0 = k3_subset_1(sK1,sK1) | (~spl5_31 | ~spl5_32)),
% 1.40/0.58    inference(subsumption_resolution,[],[f617,f561])).
% 1.40/0.58  fof(f561,plain,(
% 1.40/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl5_31),
% 1.40/0.58    inference(avatar_component_clause,[],[f560])).
% 1.40/0.58  fof(f560,plain,(
% 1.40/0.58    spl5_31 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.40/0.58  fof(f617,plain,(
% 1.40/0.58    k1_xboole_0 = k3_subset_1(sK1,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl5_32),
% 1.40/0.58    inference(superposition,[],[f51,f566])).
% 1.40/0.58  fof(f566,plain,(
% 1.40/0.58    sK1 = k3_subset_1(sK1,k1_xboole_0) | ~spl5_32),
% 1.40/0.58    inference(avatar_component_clause,[],[f564])).
% 1.40/0.58  fof(f564,plain,(
% 1.40/0.58    spl5_32 <=> sK1 = k3_subset_1(sK1,k1_xboole_0)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.40/0.58  fof(f51,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.58    inference(cnf_transformation,[],[f22])).
% 1.40/0.58  fof(f22,plain,(
% 1.40/0.58    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.58    inference(ennf_transformation,[],[f12])).
% 1.40/0.58  fof(f12,axiom,(
% 1.40/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.40/0.58  fof(f175,plain,(
% 1.40/0.58    sK1 = k3_subset_1(sK1,sK1) | ~spl5_6),
% 1.40/0.58    inference(avatar_component_clause,[],[f173])).
% 1.40/0.58  fof(f173,plain,(
% 1.40/0.58    spl5_6 <=> sK1 = k3_subset_1(sK1,sK1)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.40/0.58  fof(f615,plain,(
% 1.40/0.58    ~spl5_7 | spl5_31),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f614])).
% 1.40/0.58  fof(f614,plain,(
% 1.40/0.58    $false | (~spl5_7 | spl5_31)),
% 1.40/0.58    inference(subsumption_resolution,[],[f596,f42])).
% 1.40/0.58  fof(f42,plain,(
% 1.40/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f4])).
% 1.40/0.58  fof(f4,axiom,(
% 1.40/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.40/0.58  fof(f596,plain,(
% 1.40/0.58    ( ! [X9] : (~r1_tarski(k1_xboole_0,k5_xboole_0(X9,k3_xboole_0(X9,sK2)))) ) | (~spl5_7 | spl5_31)),
% 1.40/0.58    inference(resolution,[],[f580,f95])).
% 1.40/0.58  fof(f95,plain,(
% 1.40/0.58    ( ! [X2,X1] : (r1_xboole_0(X2,sK1) | ~r1_tarski(X2,k5_xboole_0(X1,k3_xboole_0(X1,sK2)))) )),
% 1.40/0.58    inference(superposition,[],[f67,f86])).
% 1.40/0.58  fof(f86,plain,(
% 1.40/0.58    ( ! [X0] : (sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK2))))) )),
% 1.40/0.58    inference(resolution,[],[f72,f39])).
% 1.40/0.58  fof(f39,plain,(
% 1.40/0.58    r1_tarski(sK1,sK2)),
% 1.40/0.58    inference(cnf_transformation,[],[f27])).
% 1.40/0.58  fof(f72,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X0) )),
% 1.40/0.58    inference(resolution,[],[f67,f66])).
% 1.40/0.58  fof(f66,plain,(
% 1.40/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.40/0.58    inference(definition_unfolding,[],[f52,f43])).
% 1.40/0.58  fof(f43,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.40/0.58    inference(cnf_transformation,[],[f2])).
% 1.40/0.58  fof(f2,axiom,(
% 1.40/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.40/0.58  fof(f52,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f29])).
% 1.40/0.58  fof(f29,plain,(
% 1.40/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.40/0.58    inference(nnf_transformation,[],[f6])).
% 1.40/0.58  fof(f6,axiom,(
% 1.40/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.40/0.58  fof(f67,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.40/0.58    inference(definition_unfolding,[],[f61,f43])).
% 1.40/0.58  fof(f61,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f24])).
% 1.40/0.58  fof(f24,plain,(
% 1.40/0.58    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.40/0.58    inference(ennf_transformation,[],[f7])).
% 1.40/0.58  fof(f7,axiom,(
% 1.40/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.40/0.58  fof(f580,plain,(
% 1.40/0.58    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0)) ) | (~spl5_7 | spl5_31)),
% 1.40/0.58    inference(subsumption_resolution,[],[f576,f42])).
% 1.40/0.58  fof(f576,plain,(
% 1.40/0.58    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~r1_xboole_0(k1_xboole_0,X0)) ) | (~spl5_7 | spl5_31)),
% 1.40/0.58    inference(resolution,[],[f575,f48])).
% 1.40/0.58  fof(f48,plain,(
% 1.40/0.58    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f19])).
% 1.40/0.58  fof(f19,plain,(
% 1.40/0.58    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.40/0.58    inference(flattening,[],[f18])).
% 1.40/0.58  fof(f18,plain,(
% 1.40/0.58    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.40/0.58    inference(ennf_transformation,[],[f5])).
% 1.40/0.58  fof(f5,axiom,(
% 1.40/0.58    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.40/0.58  fof(f575,plain,(
% 1.40/0.58    ~v1_xboole_0(k1_xboole_0) | (~spl5_7 | spl5_31)),
% 1.40/0.58    inference(subsumption_resolution,[],[f574,f181])).
% 1.40/0.58  fof(f181,plain,(
% 1.40/0.58    v1_xboole_0(k1_zfmisc_1(sK1)) | ~spl5_7),
% 1.40/0.58    inference(avatar_component_clause,[],[f180])).
% 1.40/0.58  fof(f180,plain,(
% 1.40/0.58    spl5_7 <=> v1_xboole_0(k1_zfmisc_1(sK1))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.40/0.58  fof(f574,plain,(
% 1.40/0.58    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_31),
% 1.40/0.58    inference(resolution,[],[f562,f47])).
% 1.40/0.58  fof(f47,plain,(
% 1.40/0.58    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f28])).
% 1.40/0.58  fof(f28,plain,(
% 1.40/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.40/0.58    inference(nnf_transformation,[],[f17])).
% 1.40/0.58  fof(f17,plain,(
% 1.40/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.40/0.58    inference(ennf_transformation,[],[f9])).
% 1.40/0.58  fof(f9,axiom,(
% 1.40/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.40/0.58  fof(f562,plain,(
% 1.40/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl5_31),
% 1.40/0.58    inference(avatar_component_clause,[],[f560])).
% 1.40/0.58  fof(f568,plain,(
% 1.40/0.58    ~spl5_31 | spl5_32),
% 1.40/0.58    inference(avatar_split_clause,[],[f534,f564,f560])).
% 1.40/0.58  fof(f534,plain,(
% 1.40/0.58    sK1 = k3_subset_1(sK1,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 1.40/0.58    inference(superposition,[],[f506,f64])).
% 1.40/0.58  fof(f64,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.58    inference(definition_unfolding,[],[f50,f43])).
% 1.40/0.58  fof(f50,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.58    inference(cnf_transformation,[],[f21])).
% 1.40/0.58  fof(f21,plain,(
% 1.40/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.58    inference(ennf_transformation,[],[f10])).
% 1.40/0.58  fof(f10,axiom,(
% 1.40/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.40/0.58  fof(f506,plain,(
% 1.40/0.58    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))),
% 1.40/0.58    inference(superposition,[],[f87,f192])).
% 1.40/0.58  fof(f192,plain,(
% 1.40/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.40/0.58    inference(resolution,[],[f73,f42])).
% 1.40/0.58  fof(f73,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = X0) )),
% 1.40/0.58    inference(resolution,[],[f68,f66])).
% 1.40/0.58  fof(f68,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 1.40/0.58    inference(definition_unfolding,[],[f63,f43])).
% 1.40/0.58  fof(f63,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 1.40/0.58    inference(cnf_transformation,[],[f25])).
% 1.40/0.58  fof(f25,plain,(
% 1.40/0.58    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.40/0.58    inference(ennf_transformation,[],[f3])).
% 1.40/0.58  fof(f3,axiom,(
% 1.40/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.40/0.58  fof(f87,plain,(
% 1.40/0.58    ( ! [X1] : (sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(sK0,sK2)))))) )),
% 1.40/0.58    inference(resolution,[],[f72,f40])).
% 1.40/0.58  fof(f40,plain,(
% 1.40/0.58    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.40/0.58    inference(cnf_transformation,[],[f27])).
% 1.40/0.58  fof(f558,plain,(
% 1.40/0.58    ~spl5_6 | spl5_7),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f557])).
% 1.40/0.58  fof(f557,plain,(
% 1.40/0.58    $false | (~spl5_6 | spl5_7)),
% 1.40/0.58    inference(subsumption_resolution,[],[f556,f41])).
% 1.40/0.58  fof(f556,plain,(
% 1.40/0.58    k1_xboole_0 = sK1 | (~spl5_6 | spl5_7)),
% 1.40/0.58    inference(forward_demodulation,[],[f175,f546])).
% 1.40/0.58  fof(f546,plain,(
% 1.40/0.58    k1_xboole_0 = k3_subset_1(sK1,sK1) | spl5_7),
% 1.40/0.58    inference(subsumption_resolution,[],[f544,f327])).
% 1.40/0.58  fof(f327,plain,(
% 1.40/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl5_7),
% 1.40/0.58    inference(resolution,[],[f317,f42])).
% 1.40/0.58  fof(f317,plain,(
% 1.40/0.58    ( ! [X0] : (~r1_tarski(X0,sK1) | m1_subset_1(X0,k1_zfmisc_1(sK1))) ) | spl5_7),
% 1.40/0.58    inference(resolution,[],[f189,f70])).
% 1.40/0.58  fof(f70,plain,(
% 1.40/0.58    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.40/0.58    inference(equality_resolution,[],[f58])).
% 1.40/0.58  fof(f58,plain,(
% 1.40/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.40/0.58    inference(cnf_transformation,[],[f37])).
% 1.40/0.58  fof(f37,plain,(
% 1.40/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.40/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 1.40/0.58  fof(f36,plain,(
% 1.40/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.40/0.58    introduced(choice_axiom,[])).
% 1.40/0.58  fof(f35,plain,(
% 1.40/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.40/0.58    inference(rectify,[],[f34])).
% 1.40/0.58  fof(f34,plain,(
% 1.40/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.40/0.58    inference(nnf_transformation,[],[f8])).
% 1.40/0.58  fof(f8,axiom,(
% 1.40/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.40/0.58  fof(f189,plain,(
% 1.40/0.58    ( ! [X1] : (~r2_hidden(X1,k1_zfmisc_1(sK1)) | m1_subset_1(X1,k1_zfmisc_1(sK1))) ) | spl5_7),
% 1.40/0.58    inference(resolution,[],[f182,f45])).
% 1.40/0.58  fof(f45,plain,(
% 1.40/0.58    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f28])).
% 1.40/0.58  fof(f182,plain,(
% 1.40/0.58    ~v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_7),
% 1.40/0.58    inference(avatar_component_clause,[],[f180])).
% 1.40/0.58  fof(f544,plain,(
% 1.40/0.58    k1_xboole_0 = k3_subset_1(sK1,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl5_7),
% 1.40/0.58    inference(superposition,[],[f51,f540])).
% 1.40/0.58  fof(f540,plain,(
% 1.40/0.58    sK1 = k3_subset_1(sK1,k1_xboole_0) | spl5_7),
% 1.40/0.58    inference(subsumption_resolution,[],[f534,f327])).
% 1.40/0.58  fof(f549,plain,(
% 1.40/0.58    spl5_5 | spl5_7),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f548])).
% 1.40/0.58  fof(f548,plain,(
% 1.40/0.58    $false | (spl5_5 | spl5_7)),
% 1.40/0.58    inference(subsumption_resolution,[],[f547,f327])).
% 1.40/0.58  fof(f547,plain,(
% 1.40/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | (spl5_5 | spl5_7)),
% 1.40/0.58    inference(subsumption_resolution,[],[f545,f171])).
% 1.40/0.58  fof(f171,plain,(
% 1.40/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl5_5),
% 1.40/0.58    inference(avatar_component_clause,[],[f169])).
% 1.40/0.58  fof(f169,plain,(
% 1.40/0.58    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.40/0.58  fof(f545,plain,(
% 1.40/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl5_7),
% 1.40/0.58    inference(superposition,[],[f49,f540])).
% 1.40/0.58  fof(f49,plain,(
% 1.40/0.58    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.58    inference(cnf_transformation,[],[f20])).
% 1.40/0.58  fof(f20,plain,(
% 1.40/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.58    inference(ennf_transformation,[],[f11])).
% 1.40/0.58  fof(f11,axiom,(
% 1.40/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.40/0.58  fof(f407,plain,(
% 1.40/0.58    spl5_8),
% 1.40/0.58    inference(avatar_contradiction_clause,[],[f406])).
% 1.40/0.58  fof(f406,plain,(
% 1.40/0.58    $false | spl5_8),
% 1.40/0.58    inference(subsumption_resolution,[],[f402,f150])).
% 1.40/0.58  fof(f150,plain,(
% 1.40/0.58    r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 1.40/0.58    inference(trivial_inequality_removal,[],[f149])).
% 1.40/0.58  fof(f149,plain,(
% 1.40/0.58    sK1 != sK1 | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 1.40/0.58    inference(superposition,[],[f65,f111])).
% 1.40/0.58  fof(f111,plain,(
% 1.40/0.58    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK2)))),
% 1.40/0.58    inference(resolution,[],[f92,f38])).
% 1.40/0.58  fof(f38,plain,(
% 1.40/0.58    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.40/0.58    inference(cnf_transformation,[],[f27])).
% 1.40/0.58  fof(f92,plain,(
% 1.40/0.58    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(X0,sK2)))) )),
% 1.40/0.58    inference(superposition,[],[f86,f64])).
% 1.40/0.58  fof(f65,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 1.40/0.58    inference(definition_unfolding,[],[f53,f43])).
% 1.40/0.58  fof(f53,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.40/0.58    inference(cnf_transformation,[],[f29])).
% 1.40/0.58  fof(f402,plain,(
% 1.40/0.58    ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | spl5_8),
% 1.40/0.58    inference(resolution,[],[f390,f40])).
% 1.40/0.58  fof(f390,plain,(
% 1.40/0.58    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r1_xboole_0(sK1,X0)) ) | spl5_8),
% 1.40/0.58    inference(resolution,[],[f186,f48])).
% 1.40/0.58  fof(f186,plain,(
% 1.40/0.58    ~v1_xboole_0(sK1) | spl5_8),
% 1.40/0.58    inference(avatar_component_clause,[],[f184])).
% 1.40/0.58  fof(f184,plain,(
% 1.40/0.58    spl5_8 <=> v1_xboole_0(sK1)),
% 1.40/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.40/0.58  fof(f187,plain,(
% 1.40/0.58    ~spl5_7 | ~spl5_8 | spl5_5),
% 1.40/0.58    inference(avatar_split_clause,[],[f178,f169,f184,f180])).
% 1.40/0.58  fof(f178,plain,(
% 1.40/0.58    ~v1_xboole_0(sK1) | ~v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_5),
% 1.40/0.58    inference(resolution,[],[f171,f47])).
% 1.40/0.58  fof(f177,plain,(
% 1.40/0.58    ~spl5_5 | spl5_6),
% 1.40/0.58    inference(avatar_split_clause,[],[f164,f173,f169])).
% 1.40/0.58  fof(f164,plain,(
% 1.40/0.58    sK1 = k3_subset_1(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 1.40/0.58    inference(superposition,[],[f64,f146])).
% 1.40/0.58  fof(f146,plain,(
% 1.40/0.58    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))),
% 1.40/0.58    inference(superposition,[],[f87,f111])).
% 1.40/0.58  % SZS output end Proof for theBenchmark
% 1.40/0.58  % (9215)------------------------------
% 1.40/0.58  % (9215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (9215)Termination reason: Refutation
% 1.40/0.58  
% 1.40/0.58  % (9215)Memory used [KB]: 11001
% 1.40/0.58  % (9215)Time elapsed: 0.171 s
% 1.40/0.58  % (9215)------------------------------
% 1.40/0.58  % (9215)------------------------------
% 1.40/0.58  % (9211)Success in time 0.211 s
%------------------------------------------------------------------------------
