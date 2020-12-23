%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 162 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  257 ( 579 expanded)
%              Number of equality atoms :   26 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f586,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f70,f80,f90,f123,f157,f585])).

fof(f585,plain,
    ( ~ spl4_8
    | spl4_2
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f584,f78,f62,f65,f138])).

fof(f138,plain,
    ( spl4_8
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f65,plain,
    ( spl4_2
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f62,plain,
    ( spl4_1
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f78,plain,
    ( spl4_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f584,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_tarski(sK1,sK0)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f553,f81])).

fof(f81,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f33,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | ~ r1_xboole_0(sK1,sK2) )
    & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | r1_xboole_0(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
            | ~ r1_xboole_0(sK1,X2) )
          & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
            | r1_xboole_0(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
          | ~ r1_xboole_0(sK1,X2) )
        & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
          | r1_xboole_0(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | ~ r1_xboole_0(sK1,sK2) )
      & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | r1_xboole_0(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f553,plain,
    ( ! [X1] :
        ( r1_tarski(sK1,k5_xboole_0(X1,k3_xboole_0(X1,sK2)))
        | ~ r1_tarski(sK1,X1) )
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f126,f390])).

fof(f390,plain,
    ( sK1 = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_4 ),
    inference(superposition,[],[f55,f384])).

fof(f384,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_4 ),
    inference(resolution,[],[f131,f37])).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK0,X0)
        | k1_xboole_0 = k3_xboole_0(sK1,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f93,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK1,X0)
        | ~ r1_xboole_0(sK0,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f91,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f91,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f79,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f79,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f126,plain,
    ( ! [X1] :
        ( r1_tarski(k5_xboole_0(sK1,k1_xboole_0),k5_xboole_0(X1,k3_xboole_0(X1,sK2)))
        | ~ r1_tarski(sK1,X1) )
    | ~ spl4_1 ),
    inference(superposition,[],[f58,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f68,f47])).

fof(f68,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f41,f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f157,plain,
    ( ~ spl4_4
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl4_4
    | spl4_8 ),
    inference(subsumption_resolution,[],[f91,f139])).

fof(f139,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f123,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f63,f103])).

fof(f103,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f101,f88])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k3_subset_1(sK0,sK2),X0)
        | r1_xboole_0(sK1,X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f69,f54])).

fof(f69,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f101,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) ),
    inference(superposition,[],[f56,f81])).

fof(f56,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f63,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f90,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl4_3 ),
    inference(resolution,[],[f76,f36])).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f76,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f80,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f72,f78,f75])).

fof(f72,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f34,f65,f62])).

fof(f34,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f35,f65,f62])).

fof(f35,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (927)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.48  % (936)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.49  % (927)Refutation not found, incomplete strategy% (927)------------------------------
% 0.21/0.49  % (927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (927)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (927)Memory used [KB]: 10618
% 0.21/0.50  % (927)Time elapsed: 0.072 s
% 0.21/0.50  % (927)------------------------------
% 0.21/0.50  % (927)------------------------------
% 0.21/0.52  % (924)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (911)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (915)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (931)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (914)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (913)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (912)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (907)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (925)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (910)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (938)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (939)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (916)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (937)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (940)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (911)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f586,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f67,f70,f80,f90,f123,f157,f585])).
% 0.21/0.55  fof(f585,plain,(
% 0.21/0.55    ~spl4_8 | spl4_2 | ~spl4_1 | ~spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f584,f78,f62,f65,f138])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    spl4_8 <=> r1_tarski(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    spl4_2 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    spl4_1 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    spl4_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.55  fof(f584,plain,(
% 0.21/0.55    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_tarski(sK1,sK0) | (~spl4_1 | ~spl4_4)),
% 0.21/0.55    inference(superposition,[],[f553,f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 0.21/0.55    inference(resolution,[],[f33,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f46,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.55    inference(negated_conjecture,[],[f13])).
% 0.21/0.55  fof(f13,conjecture,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.21/0.55  fof(f553,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(sK1,k5_xboole_0(X1,k3_xboole_0(X1,sK2))) | ~r1_tarski(sK1,X1)) ) | (~spl4_1 | ~spl4_4)),
% 0.21/0.55    inference(backward_demodulation,[],[f126,f390])).
% 0.21/0.55  fof(f390,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(sK1,k1_xboole_0) | ~spl4_4),
% 0.21/0.55    inference(superposition,[],[f55,f384])).
% 0.21/0.55  fof(f384,plain,(
% 0.21/0.55    k1_xboole_0 = k3_xboole_0(sK1,k1_xboole_0) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f131,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_xboole_0(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK1,X0)) ) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f93,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X0] : (r1_xboole_0(sK1,X0) | ~r1_xboole_0(sK0,X0)) ) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f91,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    r1_tarski(sK1,sK0) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f79,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(rectify,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f78])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f38,f41])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(k5_xboole_0(sK1,k1_xboole_0),k5_xboole_0(X1,k3_xboole_0(X1,sK2))) | ~r1_tarski(sK1,X1)) ) | ~spl4_1),
% 0.21/0.55    inference(superposition,[],[f58,f124])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl4_1),
% 0.21/0.55    inference(resolution,[],[f68,f47])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    r1_xboole_0(sK1,sK2) | ~spl4_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f62])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f53,f41,f41])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    ~spl4_4 | spl4_8),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.55  fof(f156,plain,(
% 0.21/0.55    $false | (~spl4_4 | spl4_8)),
% 0.21/0.55    inference(subsumption_resolution,[],[f91,f139])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    ~r1_tarski(sK1,sK0) | spl4_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f138])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    spl4_1 | ~spl4_2),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    $false | (spl4_1 | ~spl4_2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f63,f103])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    r1_xboole_0(sK1,sK2) | ~spl4_2),
% 0.21/0.55    inference(resolution,[],[f101,f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_xboole_0(k3_subset_1(sK0,sK2),X0) | r1_xboole_0(sK1,X0)) ) | ~spl4_2),
% 0.21/0.55    inference(resolution,[],[f69,f54])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl4_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f65])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 0.21/0.55    inference(superposition,[],[f56,f81])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f39,f41])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ~r1_xboole_0(sK1,sK2) | spl4_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f62])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ~spl4_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f89])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    $false | ~spl4_3),
% 0.21/0.55    inference(resolution,[],[f76,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    spl4_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    spl4_3 | spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f72,f78,f75])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(resolution,[],[f32,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    spl4_1 | spl4_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f34,f65,f62])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ~spl4_1 | ~spl4_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f35,f65,f62])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (911)------------------------------
% 0.21/0.55  % (911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (911)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (911)Memory used [KB]: 11001
% 0.21/0.55  % (911)Time elapsed: 0.138 s
% 0.21/0.55  % (911)------------------------------
% 0.21/0.55  % (911)------------------------------
% 0.21/0.55  % (904)Success in time 0.187 s
%------------------------------------------------------------------------------
