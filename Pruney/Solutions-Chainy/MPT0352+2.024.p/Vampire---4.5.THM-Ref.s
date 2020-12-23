%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:17 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 139 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  222 ( 336 expanded)
%              Number of equality atoms :    7 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f769,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f104,f126,f147,f152,f180,f191,f768])).

fof(f768,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f767])).

fof(f767,plain,
    ( $false
    | spl5_3
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f102,f764])).

fof(f764,plain,
    ( ! [X0] : ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(X0,sK1))
    | spl5_3
    | ~ spl5_9 ),
    inference(resolution,[],[f753,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f753,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k2_xboole_0(sK2,k4_xboole_0(X0,sK1)))
    | spl5_3
    | ~ spl5_9 ),
    inference(resolution,[],[f406,f146])).

fof(f146,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_9
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f406,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(sK1,X3)
        | ~ r1_tarski(X3,k2_xboole_0(sK2,k4_xboole_0(X4,sK1))) )
    | spl5_3 ),
    inference(resolution,[],[f304,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f304,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(X0,sK1)))
    | spl5_3 ),
    inference(resolution,[],[f218,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK1)
        | ~ r1_tarski(sK1,k2_xboole_0(sK2,X0)) )
    | spl5_3 ),
    inference(resolution,[],[f193,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK1,X0)
        | ~ r1_tarski(sK1,k2_xboole_0(sK2,X0)) )
    | spl5_3 ),
    inference(resolution,[],[f99,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f99,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f102,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_4
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f191,plain,
    ( spl5_4
    | ~ spl5_1
    | ~ spl5_2
    | spl5_14 ),
    inference(avatar_split_clause,[],[f190,f177,f82,f77,f101])).

fof(f77,plain,
    ( spl5_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f82,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f177,plain,
    ( spl5_14
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f190,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_2
    | spl5_14 ),
    inference(subsumption_resolution,[],[f94,f186])).

fof(f186,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_14 ),
    inference(resolution,[],[f179,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f179,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f177])).

fof(f94,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | r1_tarski(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f88,f91])).

fof(f91,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f88,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f38,f86])).

fof(f86,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f79,f56])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f38,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f180,plain,
    ( ~ spl5_14
    | spl5_10 ),
    inference(avatar_split_clause,[],[f157,f149,f177])).

fof(f149,plain,
    ( spl5_10
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f157,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl5_10 ),
    inference(resolution,[],[f151,f53])).

fof(f151,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f152,plain,
    ( ~ spl5_10
    | spl5_4 ),
    inference(avatar_split_clause,[],[f116,f101,f149])).

fof(f116,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f113,f46])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f113,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,sK2),sK0)
    | spl5_4 ),
    inference(resolution,[],[f103,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f103,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f147,plain,
    ( spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f130,f123,f144])).

fof(f123,plain,
    ( spl5_6
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f130,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f125,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f125,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f126,plain,
    ( spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f95,f82,f123])).

fof(f95,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f92,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f92,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f84,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f104,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f93,f82,f77,f101,f97])).

fof(f93,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f89,f91])).

fof(f89,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f39,f86])).

fof(f39,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:12:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (28820)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (28801)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (28799)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (28806)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (28804)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (28812)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (28821)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (28800)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (28816)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (28813)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (28811)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (28819)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.52/0.55  % (28810)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.55  % (28798)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.52/0.55  % (28808)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.52/0.55  % (28827)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.56  % (28807)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.52/0.56  % (28818)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.52/0.56  % (28814)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.52/0.56  % (28805)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.52/0.56  % (28802)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.52/0.57  % (28822)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.52/0.57  % (28803)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.52/0.57  % (28815)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.65/0.57  % (28826)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.65/0.57  % (28809)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.65/0.58  % (28825)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.65/0.58  % (28823)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.65/0.58  % (28824)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.65/0.59  % (28817)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.65/0.60  % (28818)Refutation found. Thanks to Tanya!
% 1.65/0.60  % SZS status Theorem for theBenchmark
% 1.65/0.61  % SZS output start Proof for theBenchmark
% 1.65/0.61  fof(f769,plain,(
% 1.65/0.61    $false),
% 1.65/0.61    inference(avatar_sat_refutation,[],[f80,f85,f104,f126,f147,f152,f180,f191,f768])).
% 1.65/0.61  fof(f768,plain,(
% 1.65/0.61    spl5_3 | ~spl5_4 | ~spl5_9),
% 1.65/0.61    inference(avatar_contradiction_clause,[],[f767])).
% 1.65/0.61  fof(f767,plain,(
% 1.65/0.61    $false | (spl5_3 | ~spl5_4 | ~spl5_9)),
% 1.65/0.61    inference(subsumption_resolution,[],[f102,f764])).
% 1.65/0.61  fof(f764,plain,(
% 1.65/0.61    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(X0,sK1))) ) | (spl5_3 | ~spl5_9)),
% 1.65/0.61    inference(resolution,[],[f753,f68])).
% 1.65/0.61  fof(f68,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f31])).
% 1.65/0.61  fof(f31,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.65/0.61    inference(ennf_transformation,[],[f10])).
% 1.65/0.61  fof(f10,axiom,(
% 1.65/0.61    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.65/0.61  fof(f753,plain,(
% 1.65/0.61    ( ! [X0] : (~r1_tarski(sK0,k2_xboole_0(sK2,k4_xboole_0(X0,sK1)))) ) | (spl5_3 | ~spl5_9)),
% 1.65/0.61    inference(resolution,[],[f406,f146])).
% 1.65/0.61  fof(f146,plain,(
% 1.65/0.61    r1_tarski(sK1,sK0) | ~spl5_9),
% 1.65/0.61    inference(avatar_component_clause,[],[f144])).
% 1.65/0.61  fof(f144,plain,(
% 1.65/0.61    spl5_9 <=> r1_tarski(sK1,sK0)),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.65/0.61  fof(f406,plain,(
% 1.65/0.61    ( ! [X4,X3] : (~r1_tarski(sK1,X3) | ~r1_tarski(X3,k2_xboole_0(sK2,k4_xboole_0(X4,sK1)))) ) | spl5_3),
% 1.65/0.61    inference(resolution,[],[f304,f70])).
% 1.65/0.61  fof(f70,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f35])).
% 1.65/0.61  fof(f35,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.65/0.61    inference(flattening,[],[f34])).
% 1.65/0.61  fof(f34,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.65/0.61    inference(ennf_transformation,[],[f7])).
% 1.65/0.61  fof(f7,axiom,(
% 1.65/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.65/0.61  fof(f304,plain,(
% 1.65/0.61    ( ! [X0] : (~r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(X0,sK1)))) ) | spl5_3),
% 1.65/0.61    inference(resolution,[],[f218,f43])).
% 1.65/0.61  fof(f43,plain,(
% 1.65/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f12])).
% 1.65/0.61  fof(f12,axiom,(
% 1.65/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.65/0.61  fof(f218,plain,(
% 1.65/0.61    ( ! [X0] : (~r1_xboole_0(X0,sK1) | ~r1_tarski(sK1,k2_xboole_0(sK2,X0))) ) | spl5_3),
% 1.65/0.61    inference(resolution,[],[f193,f53])).
% 1.65/0.61  fof(f53,plain,(
% 1.65/0.61    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f25])).
% 1.65/0.61  fof(f25,plain,(
% 1.65/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.65/0.61    inference(ennf_transformation,[],[f3])).
% 1.65/0.61  fof(f3,axiom,(
% 1.65/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.65/0.61  fof(f193,plain,(
% 1.65/0.61    ( ! [X0] : (~r1_xboole_0(sK1,X0) | ~r1_tarski(sK1,k2_xboole_0(sK2,X0))) ) | spl5_3),
% 1.65/0.61    inference(resolution,[],[f99,f71])).
% 1.65/0.61  fof(f71,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.65/0.61    inference(cnf_transformation,[],[f37])).
% 1.65/0.61  fof(f37,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.65/0.61    inference(flattening,[],[f36])).
% 1.65/0.61  fof(f36,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.65/0.61    inference(ennf_transformation,[],[f11])).
% 1.65/0.61  fof(f11,axiom,(
% 1.65/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.65/0.61  fof(f99,plain,(
% 1.65/0.61    ~r1_tarski(sK1,sK2) | spl5_3),
% 1.65/0.61    inference(avatar_component_clause,[],[f97])).
% 1.65/0.61  fof(f97,plain,(
% 1.65/0.61    spl5_3 <=> r1_tarski(sK1,sK2)),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.65/0.61  fof(f102,plain,(
% 1.65/0.61    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl5_4),
% 1.65/0.61    inference(avatar_component_clause,[],[f101])).
% 1.65/0.61  fof(f101,plain,(
% 1.65/0.61    spl5_4 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.65/0.61  fof(f191,plain,(
% 1.65/0.61    spl5_4 | ~spl5_1 | ~spl5_2 | spl5_14),
% 1.65/0.61    inference(avatar_split_clause,[],[f190,f177,f82,f77,f101])).
% 1.65/0.61  fof(f77,plain,(
% 1.65/0.61    spl5_1 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.65/0.61  fof(f82,plain,(
% 1.65/0.61    spl5_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.65/0.61  fof(f177,plain,(
% 1.65/0.61    spl5_14 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.65/0.61  fof(f190,plain,(
% 1.65/0.61    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl5_1 | ~spl5_2 | spl5_14)),
% 1.65/0.61    inference(subsumption_resolution,[],[f94,f186])).
% 1.65/0.61  fof(f186,plain,(
% 1.65/0.61    ~r1_tarski(sK1,sK2) | spl5_14),
% 1.65/0.61    inference(resolution,[],[f179,f67])).
% 1.65/0.61  fof(f67,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f30])).
% 1.65/0.61  fof(f30,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.65/0.61    inference(ennf_transformation,[],[f14])).
% 1.65/0.61  fof(f14,axiom,(
% 1.65/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.65/0.61  fof(f179,plain,(
% 1.65/0.61    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl5_14),
% 1.65/0.61    inference(avatar_component_clause,[],[f177])).
% 1.65/0.61  fof(f94,plain,(
% 1.65/0.61    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | r1_tarski(sK1,sK2) | (~spl5_1 | ~spl5_2)),
% 1.65/0.61    inference(backward_demodulation,[],[f88,f91])).
% 1.65/0.61  fof(f91,plain,(
% 1.65/0.61    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl5_2),
% 1.65/0.61    inference(resolution,[],[f84,f56])).
% 1.65/0.61  fof(f56,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f28])).
% 1.65/0.61  fof(f28,plain,(
% 1.65/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f19])).
% 1.65/0.61  fof(f19,axiom,(
% 1.65/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.65/0.61  fof(f84,plain,(
% 1.65/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.65/0.61    inference(avatar_component_clause,[],[f82])).
% 1.65/0.61  fof(f88,plain,(
% 1.65/0.61    r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2) | ~spl5_1),
% 1.65/0.61    inference(backward_demodulation,[],[f38,f86])).
% 1.65/0.61  fof(f86,plain,(
% 1.65/0.61    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl5_1),
% 1.65/0.61    inference(resolution,[],[f79,f56])).
% 1.65/0.61  fof(f79,plain,(
% 1.65/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl5_1),
% 1.65/0.61    inference(avatar_component_clause,[],[f77])).
% 1.65/0.61  fof(f38,plain,(
% 1.65/0.61    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 1.65/0.61    inference(cnf_transformation,[],[f23])).
% 1.65/0.61  fof(f23,plain,(
% 1.65/0.61    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f22])).
% 1.65/0.61  fof(f22,negated_conjecture,(
% 1.65/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.65/0.61    inference(negated_conjecture,[],[f21])).
% 1.65/0.61  fof(f21,conjecture,(
% 1.65/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 1.65/0.61  fof(f180,plain,(
% 1.65/0.61    ~spl5_14 | spl5_10),
% 1.65/0.61    inference(avatar_split_clause,[],[f157,f149,f177])).
% 1.65/0.61  fof(f149,plain,(
% 1.65/0.61    spl5_10 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.65/0.61  fof(f157,plain,(
% 1.65/0.61    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl5_10),
% 1.65/0.61    inference(resolution,[],[f151,f53])).
% 1.65/0.61  fof(f151,plain,(
% 1.65/0.61    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl5_10),
% 1.65/0.61    inference(avatar_component_clause,[],[f149])).
% 1.65/0.61  fof(f152,plain,(
% 1.65/0.61    ~spl5_10 | spl5_4),
% 1.65/0.61    inference(avatar_split_clause,[],[f116,f101,f149])).
% 1.65/0.61  fof(f116,plain,(
% 1.65/0.61    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | spl5_4),
% 1.65/0.61    inference(subsumption_resolution,[],[f113,f46])).
% 1.65/0.61  fof(f46,plain,(
% 1.65/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f9])).
% 1.65/0.61  fof(f9,axiom,(
% 1.65/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.65/0.61  fof(f113,plain,(
% 1.65/0.61    ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~r1_tarski(k4_xboole_0(sK0,sK2),sK0) | spl5_4),
% 1.65/0.61    inference(resolution,[],[f103,f69])).
% 1.65/0.61  fof(f69,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f33])).
% 1.65/0.61  fof(f33,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.65/0.61    inference(flattening,[],[f32])).
% 1.65/0.61  fof(f32,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.65/0.61    inference(ennf_transformation,[],[f15])).
% 1.65/0.61  fof(f15,axiom,(
% 1.65/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.65/0.61  fof(f103,plain,(
% 1.65/0.61    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl5_4),
% 1.65/0.61    inference(avatar_component_clause,[],[f101])).
% 1.65/0.61  fof(f147,plain,(
% 1.65/0.61    spl5_9 | ~spl5_6),
% 1.65/0.61    inference(avatar_split_clause,[],[f130,f123,f144])).
% 1.65/0.61  fof(f123,plain,(
% 1.65/0.61    spl5_6 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.65/0.61  fof(f130,plain,(
% 1.65/0.61    r1_tarski(sK1,sK0) | ~spl5_6),
% 1.65/0.61    inference(resolution,[],[f125,f74])).
% 1.65/0.61  fof(f74,plain,(
% 1.65/0.61    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.65/0.61    inference(equality_resolution,[],[f64])).
% 1.65/0.61  fof(f64,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.65/0.61    inference(cnf_transformation,[],[f16])).
% 1.65/0.61  fof(f16,axiom,(
% 1.65/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.65/0.61  fof(f125,plain,(
% 1.65/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_6),
% 1.65/0.61    inference(avatar_component_clause,[],[f123])).
% 1.65/0.61  fof(f126,plain,(
% 1.65/0.61    spl5_6 | ~spl5_2),
% 1.65/0.61    inference(avatar_split_clause,[],[f95,f82,f123])).
% 1.65/0.61  fof(f95,plain,(
% 1.65/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.65/0.61    inference(subsumption_resolution,[],[f92,f42])).
% 1.65/0.61  fof(f42,plain,(
% 1.65/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.65/0.61    inference(cnf_transformation,[],[f20])).
% 1.65/0.61  fof(f20,axiom,(
% 1.65/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.65/0.61  fof(f92,plain,(
% 1.65/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.65/0.61    inference(resolution,[],[f84,f52])).
% 1.65/0.61  fof(f52,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f24])).
% 1.65/0.61  fof(f24,plain,(
% 1.65/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f18])).
% 1.65/0.61  fof(f18,axiom,(
% 1.65/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.65/0.61  fof(f104,plain,(
% 1.65/0.61    ~spl5_3 | ~spl5_4 | ~spl5_1 | ~spl5_2),
% 1.65/0.61    inference(avatar_split_clause,[],[f93,f82,f77,f101,f97])).
% 1.65/0.61  fof(f93,plain,(
% 1.65/0.61    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2) | (~spl5_1 | ~spl5_2)),
% 1.65/0.61    inference(backward_demodulation,[],[f89,f91])).
% 1.65/0.61  fof(f89,plain,(
% 1.65/0.61    ~r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2) | ~spl5_1),
% 1.65/0.61    inference(backward_demodulation,[],[f39,f86])).
% 1.65/0.61  fof(f39,plain,(
% 1.65/0.61    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 1.65/0.61    inference(cnf_transformation,[],[f23])).
% 1.65/0.61  fof(f85,plain,(
% 1.65/0.61    spl5_2),
% 1.65/0.61    inference(avatar_split_clause,[],[f41,f82])).
% 1.65/0.61  fof(f41,plain,(
% 1.65/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.65/0.61    inference(cnf_transformation,[],[f23])).
% 1.65/0.61  fof(f80,plain,(
% 1.65/0.61    spl5_1),
% 1.65/0.61    inference(avatar_split_clause,[],[f40,f77])).
% 1.65/0.61  fof(f40,plain,(
% 1.65/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.65/0.61    inference(cnf_transformation,[],[f23])).
% 1.65/0.61  % SZS output end Proof for theBenchmark
% 1.65/0.61  % (28818)------------------------------
% 1.65/0.61  % (28818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.61  % (28818)Termination reason: Refutation
% 1.65/0.61  
% 1.65/0.61  % (28818)Memory used [KB]: 11513
% 1.65/0.61  % (28818)Time elapsed: 0.181 s
% 1.65/0.61  % (28818)------------------------------
% 1.65/0.61  % (28818)------------------------------
% 1.65/0.62  % (28797)Success in time 0.253 s
%------------------------------------------------------------------------------
