%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:39 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 445 expanded)
%              Number of leaves         :   19 ( 120 expanded)
%              Depth                    :   17
%              Number of atoms          :  241 (1276 expanded)
%              Number of equality atoms :   89 ( 444 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1097,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1096,f550])).

fof(f550,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f93,f548,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f548,plain,(
    sK0 != sK1 ),
    inference(subsumption_resolution,[],[f547,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f547,plain,
    ( sK0 != sK1
    | ~ r1_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f546,f154])).

fof(f154,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f37,f78,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f78,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f68,f70])).

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
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f546,plain,
    ( sK0 != sK1
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f535,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f535,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | sK0 != sK1
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK0,sK0) ),
    inference(superposition,[],[f92,f524])).

fof(f524,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f115,f354])).

fof(f354,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f353,f156])).

fof(f156,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f81,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f38,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f353,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f109,f82])).

fof(f82,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f68,f52])).

fof(f109,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f62,f64])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f46,f47,f47])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f115,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f67,f52])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f47])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f92,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | sK0 != sK1 ),
    inference(inner_rewriting,[],[f91])).

fof(f91,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f36,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f36,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f25,plain,
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

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

% (4397)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f93,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f80,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f34,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f1096,plain,(
    r1_tarski(sK0,sK1) ),
    inference(forward_demodulation,[],[f1042,f1033])).

fof(f1033,plain,(
    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1030,f93])).

fof(f1030,plain,
    ( sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK0) ),
    inference(superposition,[],[f669,f1001])).

fof(f1001,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f114,f346])).

fof(f346,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f339,f93])).

fof(f339,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ r1_tarski(sK1,sK0) ),
    inference(superposition,[],[f114,f84])).

fof(f84,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f52,f44])).

fof(f114,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f34,f67])).

fof(f669,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f668,f175])).

fof(f175,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f155,f104])).

fof(f104,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f63,f64])).

fof(f63,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f155,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f63,f81])).

fof(f668,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f125,f354])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f66,f52])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f61,f61])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1042,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) ),
    inference(superposition,[],[f74,f1010])).

fof(f1010,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f1007,f52])).

fof(f1007,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f1002,f548])).

fof(f1002,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f90,f346])).

fof(f90,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(forward_demodulation,[],[f35,f39])).

fof(f35,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f65,f44])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:18 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (4386)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (4415)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (4415)Refutation not found, incomplete strategy% (4415)------------------------------
% 0.21/0.51  % (4415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4415)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4415)Memory used [KB]: 1663
% 0.21/0.51  % (4415)Time elapsed: 0.003 s
% 0.21/0.51  % (4415)------------------------------
% 0.21/0.51  % (4415)------------------------------
% 0.21/0.51  % (4390)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (4395)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (4398)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (4400)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.53  % (4396)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.29/0.53  % (4389)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.29/0.53  % (4388)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.29/0.53  % (4398)Refutation not found, incomplete strategy% (4398)------------------------------
% 1.29/0.53  % (4398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (4398)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (4398)Memory used [KB]: 10618
% 1.29/0.53  % (4398)Time elapsed: 0.129 s
% 1.29/0.53  % (4398)------------------------------
% 1.29/0.53  % (4398)------------------------------
% 1.29/0.53  % (4405)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.29/0.54  % (4387)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.29/0.54  % (4387)Refutation not found, incomplete strategy% (4387)------------------------------
% 1.29/0.54  % (4387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (4387)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (4387)Memory used [KB]: 1663
% 1.29/0.54  % (4387)Time elapsed: 0.127 s
% 1.29/0.54  % (4387)------------------------------
% 1.29/0.54  % (4387)------------------------------
% 1.29/0.54  % (4408)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.29/0.54  % (4412)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.42/0.54  % (4390)Refutation found. Thanks to Tanya!
% 1.42/0.54  % SZS status Theorem for theBenchmark
% 1.42/0.55  % (4404)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f1097,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(subsumption_resolution,[],[f1096,f550])).
% 1.42/0.55  fof(f550,plain,(
% 1.42/0.55    ~r1_tarski(sK0,sK1)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f93,f548,f56])).
% 1.42/0.55  fof(f56,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f29])).
% 1.42/0.55  fof(f29,plain,(
% 1.42/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.55    inference(flattening,[],[f28])).
% 1.42/0.55  fof(f28,plain,(
% 1.42/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.55    inference(nnf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.55  fof(f548,plain,(
% 1.42/0.55    sK0 != sK1),
% 1.42/0.55    inference(subsumption_resolution,[],[f547,f68])).
% 1.42/0.55  fof(f68,plain,(
% 1.42/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.42/0.55    inference(equality_resolution,[],[f55])).
% 1.42/0.55  fof(f55,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f29])).
% 1.42/0.55  fof(f547,plain,(
% 1.42/0.55    sK0 != sK1 | ~r1_tarski(sK0,sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f546,f154])).
% 1.42/0.55  fof(f154,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f37,f78,f49])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f27])).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.42/0.55    inference(nnf_transformation,[],[f20])).
% 1.42/0.55  fof(f20,plain,(
% 1.42/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f13])).
% 1.42/0.55  fof(f13,axiom,(
% 1.42/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.42/0.55  fof(f78,plain,(
% 1.42/0.55    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f68,f70])).
% 1.42/0.55  fof(f70,plain,(
% 1.42/0.55    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.42/0.55    inference(equality_resolution,[],[f58])).
% 1.42/0.55  fof(f58,plain,(
% 1.42/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f33])).
% 1.42/0.55  fof(f33,plain,(
% 1.42/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 1.42/0.55  fof(f32,plain,(
% 1.42/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f31,plain,(
% 1.42/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.42/0.55    inference(rectify,[],[f30])).
% 1.42/0.55  fof(f30,plain,(
% 1.42/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.42/0.55    inference(nnf_transformation,[],[f12])).
% 1.42/0.55  fof(f12,axiom,(
% 1.42/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.42/0.55  fof(f37,plain,(
% 1.42/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f16])).
% 1.42/0.55  fof(f16,axiom,(
% 1.42/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.42/0.55  fof(f546,plain,(
% 1.42/0.55    sK0 != sK1 | ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~r1_tarski(sK0,sK0)),
% 1.42/0.55    inference(subsumption_resolution,[],[f535,f38])).
% 1.42/0.55  fof(f38,plain,(
% 1.42/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,axiom,(
% 1.42/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.42/0.55  fof(f535,plain,(
% 1.42/0.55    ~r1_tarski(k1_xboole_0,sK0) | sK0 != sK1 | ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~r1_tarski(sK0,sK0)),
% 1.42/0.55    inference(superposition,[],[f92,f524])).
% 1.42/0.55  fof(f524,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k1_xboole_0 = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(forward_demodulation,[],[f115,f354])).
% 1.42/0.55  fof(f354,plain,(
% 1.42/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.42/0.55    inference(forward_demodulation,[],[f353,f156])).
% 1.42/0.55  fof(f156,plain,(
% 1.42/0.55    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 1.42/0.55    inference(superposition,[],[f81,f44])).
% 1.42/0.55  fof(f44,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f2])).
% 1.42/0.55  fof(f2,axiom,(
% 1.42/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.42/0.55  fof(f81,plain,(
% 1.42/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f38,f52])).
% 1.42/0.55  fof(f52,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f21,plain,(
% 1.42/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.42/0.55    inference(ennf_transformation,[],[f6])).
% 1.42/0.55  fof(f6,axiom,(
% 1.42/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.42/0.55  fof(f353,plain,(
% 1.42/0.55    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)) )),
% 1.42/0.55    inference(forward_demodulation,[],[f109,f82])).
% 1.42/0.55  fof(f82,plain,(
% 1.42/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f68,f52])).
% 1.42/0.55  fof(f109,plain,(
% 1.42/0.55    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.42/0.55    inference(superposition,[],[f62,f64])).
% 1.42/0.55  fof(f64,plain,(
% 1.42/0.55    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.42/0.55    inference(definition_unfolding,[],[f41,f47])).
% 1.42/0.55  fof(f47,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f4])).
% 1.42/0.55  fof(f4,axiom,(
% 1.42/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.42/0.55  fof(f41,plain,(
% 1.42/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.42/0.55  fof(f62,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f46,f47,f47])).
% 1.42/0.55  fof(f46,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f10])).
% 1.42/0.55  fof(f10,axiom,(
% 1.42/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.42/0.55  fof(f115,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(superposition,[],[f67,f52])).
% 1.42/0.55  fof(f67,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f53,f47])).
% 1.42/0.55  fof(f53,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f22])).
% 1.42/0.55  fof(f22,plain,(
% 1.42/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f15])).
% 1.42/0.55  fof(f15,axiom,(
% 1.42/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.42/0.55  fof(f92,plain,(
% 1.42/0.55    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | sK0 != sK1),
% 1.42/0.55    inference(inner_rewriting,[],[f91])).
% 1.42/0.55  fof(f91,plain,(
% 1.42/0.55    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.42/0.55    inference(forward_demodulation,[],[f36,f39])).
% 1.42/0.55  fof(f39,plain,(
% 1.42/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f14])).
% 1.42/0.55  fof(f14,axiom,(
% 1.42/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.42/0.55  fof(f36,plain,(
% 1.42/0.55    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f26])).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 1.42/0.55  fof(f25,plain,(
% 1.42/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f24,plain,(
% 1.42/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.42/0.55    inference(flattening,[],[f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.42/0.55    inference(nnf_transformation,[],[f19])).
% 1.42/0.55  fof(f19,plain,(
% 1.42/0.55    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f18])).
% 1.42/0.55  % (4397)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.42/0.55  fof(f18,negated_conjecture,(
% 1.42/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.42/0.55    inference(negated_conjecture,[],[f17])).
% 1.42/0.55  fof(f17,conjecture,(
% 1.42/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 1.42/0.55  fof(f93,plain,(
% 1.42/0.55    r1_tarski(sK1,sK0)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f80,f71])).
% 1.42/0.55  fof(f71,plain,(
% 1.42/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.42/0.55    inference(equality_resolution,[],[f57])).
% 1.42/0.55  fof(f57,plain,(
% 1.42/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f33])).
% 1.42/0.55  fof(f80,plain,(
% 1.42/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f37,f34,f48])).
% 1.42/0.55  fof(f48,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f27])).
% 1.42/0.55  fof(f34,plain,(
% 1.42/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.42/0.55    inference(cnf_transformation,[],[f26])).
% 1.42/0.55  fof(f1096,plain,(
% 1.42/0.55    r1_tarski(sK0,sK1)),
% 1.42/0.55    inference(forward_demodulation,[],[f1042,f1033])).
% 1.42/0.55  fof(f1033,plain,(
% 1.42/0.55    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.42/0.55    inference(subsumption_resolution,[],[f1030,f93])).
% 1.42/0.55  fof(f1030,plain,(
% 1.42/0.55    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK0)),
% 1.42/0.55    inference(superposition,[],[f669,f1001])).
% 1.42/0.55  fof(f1001,plain,(
% 1.42/0.55    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,sK1)),
% 1.42/0.55    inference(backward_demodulation,[],[f114,f346])).
% 1.42/0.55  fof(f346,plain,(
% 1.42/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f339,f93])).
% 1.42/0.55  fof(f339,plain,(
% 1.42/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~r1_tarski(sK1,sK0)),
% 1.42/0.55    inference(superposition,[],[f114,f84])).
% 1.42/0.55  fof(f84,plain,(
% 1.42/0.55    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 1.42/0.55    inference(superposition,[],[f52,f44])).
% 1.42/0.55  fof(f114,plain,(
% 1.42/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f34,f67])).
% 1.42/0.55  fof(f669,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(forward_demodulation,[],[f668,f175])).
% 1.42/0.55  fof(f175,plain,(
% 1.42/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.42/0.55    inference(backward_demodulation,[],[f155,f104])).
% 1.42/0.55  fof(f104,plain,(
% 1.42/0.55    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.42/0.55    inference(superposition,[],[f63,f64])).
% 1.42/0.55  fof(f63,plain,(
% 1.42/0.55    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 1.42/0.55    inference(definition_unfolding,[],[f40,f61])).
% 1.42/0.55  fof(f61,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f45,f47])).
% 1.42/0.55  fof(f45,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f11])).
% 1.42/0.55  fof(f11,axiom,(
% 1.42/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.42/0.55  fof(f40,plain,(
% 1.42/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f5])).
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.42/0.55  fof(f155,plain,(
% 1.42/0.55    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0) )),
% 1.42/0.55    inference(backward_demodulation,[],[f63,f81])).
% 1.42/0.55  fof(f668,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(forward_demodulation,[],[f125,f354])).
% 1.42/0.55  fof(f125,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,X0)) | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(superposition,[],[f66,f52])).
% 1.42/0.55  fof(f66,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f43,f61,f61])).
% 1.42/0.55  fof(f43,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.42/0.55  fof(f1042,plain,(
% 1.42/0.55    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)),
% 1.42/0.55    inference(superposition,[],[f74,f1010])).
% 1.42/0.55  fof(f1010,plain,(
% 1.42/0.55    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f1007,f52])).
% 1.42/0.55  fof(f1007,plain,(
% 1.42/0.55    r1_tarski(k5_xboole_0(sK0,sK1),sK1)),
% 1.42/0.55    inference(subsumption_resolution,[],[f1002,f548])).
% 1.42/0.55  fof(f1002,plain,(
% 1.42/0.55    r1_tarski(k5_xboole_0(sK0,sK1),sK1) | sK0 = sK1),
% 1.42/0.55    inference(backward_demodulation,[],[f90,f346])).
% 1.42/0.55  fof(f90,plain,(
% 1.42/0.55    r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK0 = sK1),
% 1.42/0.55    inference(forward_demodulation,[],[f35,f39])).
% 1.42/0.55  fof(f35,plain,(
% 1.42/0.55    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f26])).
% 1.42/0.55  fof(f74,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0)) )),
% 1.42/0.55    inference(superposition,[],[f65,f44])).
% 1.42/0.55  fof(f65,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f42,f47])).
% 1.42/0.55  fof(f42,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (4390)------------------------------
% 1.42/0.55  % (4390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (4390)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (4390)Memory used [KB]: 2174
% 1.42/0.55  % (4390)Time elapsed: 0.124 s
% 1.42/0.55  % (4390)------------------------------
% 1.42/0.55  % (4390)------------------------------
% 1.42/0.55  % (4411)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.42/0.55  % (4385)Success in time 0.183 s
%------------------------------------------------------------------------------
