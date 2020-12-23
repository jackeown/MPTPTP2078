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
% DateTime   : Thu Dec  3 12:44:15 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 175 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   20
%              Number of atoms          :  261 ( 637 expanded)
%              Number of equality atoms :   37 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f734,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f79,f705,f733])).

fof(f733,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f732])).

fof(f732,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f731,f72])).

fof(f72,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f731,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_2 ),
    inference(resolution,[],[f711,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f711,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(forward_demodulation,[],[f710,f202])).

fof(f202,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f53,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f710,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(forward_demodulation,[],[f77,f201])).

fof(f201,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f53,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_2
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f705,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f704])).

fof(f704,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f703,f73])).

fof(f73,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f703,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f676,f407])).

fof(f407,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f402,f44])).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f402,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f65,f384])).

fof(f384,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f117,f205])).

fof(f205,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,sK0),X0) ),
    inference(resolution,[],[f184,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f184,plain,(
    ! [X13] : r1_tarski(sK1,k2_xboole_0(sK0,X13)) ),
    inference(resolution,[],[f111,f115])).

fof(f115,plain,(
    ! [X7] :
      ( ~ r1_tarski(sK0,X7)
      | r1_tarski(sK1,X7) ) ),
    inference(superposition,[],[f63,f101])).

fof(f101,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f52,f90])).

fof(f90,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f88,f69])).

fof(f69,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f88,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f85,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f48,f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f111,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f63,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f117,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f56,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f45,f47,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f676,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f157,f328])).

fof(f328,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(resolution,[],[f327,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f327,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f294,f202])).

fof(f294,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f76,f201])).

fof(f76,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_xboole_0(X1,X0))
      | r1_tarski(k4_xboole_0(X2,X0),X1) ) ),
    inference(superposition,[],[f62,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f79,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f40,f75,f71])).

fof(f40,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f41,f75,f71])).

fof(f41,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 12:11:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.54  % (2117)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (2112)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (2120)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (2114)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (2117)Refutation not found, incomplete strategy% (2117)------------------------------
% 0.21/0.55  % (2117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2137)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (2136)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.56  % (2109)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.56  % (2128)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (2111)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.57  % (2117)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (2117)Memory used [KB]: 10874
% 0.21/0.57  % (2117)Time elapsed: 0.143 s
% 0.21/0.57  % (2117)------------------------------
% 0.21/0.57  % (2117)------------------------------
% 0.21/0.57  % (2130)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.57  % (2121)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (2134)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (2129)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.57  % (2125)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.58  % (2113)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (2119)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.58  % (2122)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.62/0.59  % (2136)Refutation not found, incomplete strategy% (2136)------------------------------
% 1.62/0.59  % (2136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (2107)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.62/0.59  % (2132)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.62/0.59  % (2136)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (2136)Memory used [KB]: 10874
% 1.62/0.59  % (2136)Time elapsed: 0.156 s
% 1.62/0.59  % (2136)------------------------------
% 1.62/0.59  % (2136)------------------------------
% 1.62/0.60  % (2131)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.62/0.60  % (2110)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.62/0.60  % (2123)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.62/0.60  % (2123)Refutation not found, incomplete strategy% (2123)------------------------------
% 1.62/0.60  % (2123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (2123)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.60  
% 1.62/0.60  % (2123)Memory used [KB]: 10618
% 1.62/0.60  % (2123)Time elapsed: 0.180 s
% 1.62/0.60  % (2123)------------------------------
% 1.62/0.60  % (2123)------------------------------
% 1.93/0.61  % (2115)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.93/0.62  % (2126)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.93/0.62  % (2135)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.93/0.62  % (2113)Refutation found. Thanks to Tanya!
% 1.93/0.62  % SZS status Theorem for theBenchmark
% 1.93/0.64  % (2118)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.93/0.64  % (2124)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.93/0.64  % SZS output start Proof for theBenchmark
% 1.93/0.64  fof(f734,plain,(
% 1.93/0.64    $false),
% 1.93/0.64    inference(avatar_sat_refutation,[],[f78,f79,f705,f733])).
% 1.93/0.64  fof(f733,plain,(
% 1.93/0.64    ~spl4_1 | spl4_2),
% 1.93/0.64    inference(avatar_contradiction_clause,[],[f732])).
% 1.93/0.64  fof(f732,plain,(
% 1.93/0.64    $false | (~spl4_1 | spl4_2)),
% 1.93/0.64    inference(subsumption_resolution,[],[f731,f72])).
% 1.93/0.64  fof(f72,plain,(
% 1.93/0.64    r1_tarski(sK1,sK2) | ~spl4_1),
% 1.93/0.64    inference(avatar_component_clause,[],[f71])).
% 1.93/0.64  fof(f71,plain,(
% 1.93/0.64    spl4_1 <=> r1_tarski(sK1,sK2)),
% 1.93/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.93/0.64  fof(f731,plain,(
% 1.93/0.64    ~r1_tarski(sK1,sK2) | spl4_2),
% 1.93/0.64    inference(resolution,[],[f711,f61])).
% 1.93/0.64  fof(f61,plain,(
% 1.93/0.64    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f22])).
% 1.93/0.64  fof(f22,plain,(
% 1.93/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.93/0.64    inference(ennf_transformation,[],[f7])).
% 1.93/0.64  fof(f7,axiom,(
% 1.93/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.93/0.64  fof(f711,plain,(
% 1.93/0.64    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl4_2),
% 1.93/0.64    inference(forward_demodulation,[],[f710,f202])).
% 1.93/0.64  fof(f202,plain,(
% 1.93/0.64    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.93/0.64    inference(resolution,[],[f53,f39])).
% 1.93/0.64  fof(f39,plain,(
% 1.93/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.93/0.64    inference(cnf_transformation,[],[f30])).
% 1.93/0.64  fof(f30,plain,(
% 1.93/0.64    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.93/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f29,f28])).
% 1.93/0.64  fof(f28,plain,(
% 1.93/0.64    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.93/0.64    introduced(choice_axiom,[])).
% 1.93/0.64  fof(f29,plain,(
% 1.93/0.64    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.93/0.64    introduced(choice_axiom,[])).
% 1.93/0.64  fof(f27,plain,(
% 1.93/0.64    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.93/0.64    inference(flattening,[],[f26])).
% 1.93/0.64  fof(f26,plain,(
% 1.93/0.64    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.93/0.64    inference(nnf_transformation,[],[f18])).
% 1.93/0.64  fof(f18,plain,(
% 1.93/0.64    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.93/0.64    inference(ennf_transformation,[],[f17])).
% 1.93/0.64  fof(f17,negated_conjecture,(
% 1.93/0.64    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.93/0.64    inference(negated_conjecture,[],[f16])).
% 1.93/0.64  fof(f16,conjecture,(
% 1.93/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 1.93/0.64  fof(f53,plain,(
% 1.93/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f21])).
% 1.93/0.64  fof(f21,plain,(
% 1.93/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.93/0.64    inference(ennf_transformation,[],[f14])).
% 1.93/0.64  fof(f14,axiom,(
% 1.93/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.93/0.64  fof(f710,plain,(
% 1.93/0.64    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl4_2),
% 1.93/0.64    inference(forward_demodulation,[],[f77,f201])).
% 1.93/0.64  fof(f201,plain,(
% 1.93/0.64    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.93/0.64    inference(resolution,[],[f53,f38])).
% 1.93/0.64  fof(f38,plain,(
% 1.93/0.64    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.93/0.64    inference(cnf_transformation,[],[f30])).
% 1.93/0.64  fof(f77,plain,(
% 1.93/0.64    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl4_2),
% 1.93/0.64    inference(avatar_component_clause,[],[f75])).
% 1.93/0.64  fof(f75,plain,(
% 1.93/0.64    spl4_2 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 1.93/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.93/0.64  fof(f705,plain,(
% 1.93/0.64    spl4_1 | ~spl4_2),
% 1.93/0.64    inference(avatar_contradiction_clause,[],[f704])).
% 1.93/0.64  fof(f704,plain,(
% 1.93/0.64    $false | (spl4_1 | ~spl4_2)),
% 1.93/0.64    inference(subsumption_resolution,[],[f703,f73])).
% 1.93/0.64  fof(f73,plain,(
% 1.93/0.64    ~r1_tarski(sK1,sK2) | spl4_1),
% 1.93/0.64    inference(avatar_component_clause,[],[f71])).
% 1.93/0.64  fof(f703,plain,(
% 1.93/0.64    r1_tarski(sK1,sK2) | ~spl4_2),
% 1.93/0.64    inference(forward_demodulation,[],[f676,f407])).
% 1.93/0.64  fof(f407,plain,(
% 1.93/0.64    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.93/0.64    inference(forward_demodulation,[],[f402,f44])).
% 1.93/0.64  fof(f44,plain,(
% 1.93/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.93/0.64    inference(cnf_transformation,[],[f8])).
% 1.93/0.64  fof(f8,axiom,(
% 1.93/0.64    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.93/0.64  fof(f402,plain,(
% 1.93/0.64    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.93/0.64    inference(superposition,[],[f65,f384])).
% 1.93/0.64  fof(f384,plain,(
% 1.93/0.64    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.93/0.64    inference(resolution,[],[f117,f205])).
% 1.93/0.64  fof(f205,plain,(
% 1.93/0.64    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,sK0),X0)) )),
% 1.93/0.64    inference(resolution,[],[f184,f62])).
% 1.93/0.64  fof(f62,plain,(
% 1.93/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f23])).
% 1.93/0.64  fof(f23,plain,(
% 1.93/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.93/0.64    inference(ennf_transformation,[],[f9])).
% 1.93/0.64  fof(f9,axiom,(
% 1.93/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.93/0.64  fof(f184,plain,(
% 1.93/0.64    ( ! [X13] : (r1_tarski(sK1,k2_xboole_0(sK0,X13))) )),
% 1.93/0.64    inference(resolution,[],[f111,f115])).
% 1.93/0.64  fof(f115,plain,(
% 1.93/0.64    ( ! [X7] : (~r1_tarski(sK0,X7) | r1_tarski(sK1,X7)) )),
% 1.93/0.64    inference(superposition,[],[f63,f101])).
% 1.93/0.64  fof(f101,plain,(
% 1.93/0.64    sK0 = k2_xboole_0(sK1,sK0)),
% 1.93/0.64    inference(resolution,[],[f52,f90])).
% 1.93/0.64  fof(f90,plain,(
% 1.93/0.64    r1_tarski(sK1,sK0)),
% 1.93/0.64    inference(resolution,[],[f88,f69])).
% 1.93/0.64  fof(f69,plain,(
% 1.93/0.64    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.93/0.64    inference(equality_resolution,[],[f57])).
% 1.93/0.64  fof(f57,plain,(
% 1.93/0.64    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.93/0.64    inference(cnf_transformation,[],[f37])).
% 1.93/0.64  fof(f37,plain,(
% 1.93/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.93/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 1.93/0.64  fof(f36,plain,(
% 1.93/0.64    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.93/0.64    introduced(choice_axiom,[])).
% 1.93/0.64  fof(f35,plain,(
% 1.93/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.93/0.64    inference(rectify,[],[f34])).
% 1.93/0.64  fof(f34,plain,(
% 1.93/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.93/0.64    inference(nnf_transformation,[],[f12])).
% 1.93/0.64  fof(f12,axiom,(
% 1.93/0.64    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.93/0.64  fof(f88,plain,(
% 1.93/0.64    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.93/0.64    inference(subsumption_resolution,[],[f85,f42])).
% 1.93/0.64  fof(f42,plain,(
% 1.93/0.64    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.93/0.64    inference(cnf_transformation,[],[f15])).
% 1.93/0.64  fof(f15,axiom,(
% 1.93/0.64    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.93/0.64  fof(f85,plain,(
% 1.93/0.64    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.93/0.64    inference(resolution,[],[f48,f38])).
% 1.93/0.64  fof(f48,plain,(
% 1.93/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f31])).
% 1.93/0.64  fof(f31,plain,(
% 1.93/0.64    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.93/0.64    inference(nnf_transformation,[],[f19])).
% 1.93/0.64  fof(f19,plain,(
% 1.93/0.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.93/0.64    inference(ennf_transformation,[],[f13])).
% 1.93/0.64  fof(f13,axiom,(
% 1.93/0.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.93/0.64  fof(f52,plain,(
% 1.93/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.93/0.64    inference(cnf_transformation,[],[f20])).
% 1.93/0.64  fof(f20,plain,(
% 1.93/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.93/0.64    inference(ennf_transformation,[],[f5])).
% 1.93/0.64  fof(f5,axiom,(
% 1.93/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.93/0.64  fof(f63,plain,(
% 1.93/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f24])).
% 1.93/0.64  fof(f24,plain,(
% 1.93/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.93/0.64    inference(ennf_transformation,[],[f4])).
% 1.93/0.64  fof(f4,axiom,(
% 1.93/0.64    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.93/0.64  fof(f111,plain,(
% 1.93/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.93/0.64    inference(resolution,[],[f63,f66])).
% 1.93/0.64  fof(f66,plain,(
% 1.93/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.93/0.64    inference(equality_resolution,[],[f55])).
% 1.93/0.64  fof(f55,plain,(
% 1.93/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.93/0.64    inference(cnf_transformation,[],[f33])).
% 1.93/0.64  fof(f33,plain,(
% 1.93/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.93/0.64    inference(flattening,[],[f32])).
% 1.93/0.64  fof(f32,plain,(
% 1.93/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.93/0.64    inference(nnf_transformation,[],[f3])).
% 1.93/0.64  fof(f3,axiom,(
% 1.93/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.93/0.64  fof(f117,plain,(
% 1.93/0.64    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.93/0.64    inference(resolution,[],[f56,f43])).
% 1.93/0.64  fof(f43,plain,(
% 1.93/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f6])).
% 1.93/0.64  fof(f6,axiom,(
% 1.93/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.93/0.64  fof(f56,plain,(
% 1.93/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f33])).
% 1.93/0.64  fof(f65,plain,(
% 1.93/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.93/0.64    inference(definition_unfolding,[],[f45,f47,f47])).
% 1.93/0.64  fof(f47,plain,(
% 1.93/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.93/0.64    inference(cnf_transformation,[],[f11])).
% 1.93/0.64  fof(f11,axiom,(
% 1.93/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.93/0.64  fof(f45,plain,(
% 1.93/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f2])).
% 1.93/0.64  fof(f2,axiom,(
% 1.93/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.93/0.64  fof(f676,plain,(
% 1.93/0.64    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) | ~spl4_2),
% 1.93/0.64    inference(resolution,[],[f157,f328])).
% 1.93/0.64  fof(f328,plain,(
% 1.93/0.64    r1_tarski(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl4_2),
% 1.93/0.64    inference(resolution,[],[f327,f64])).
% 1.93/0.64  fof(f64,plain,(
% 1.93/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.93/0.64    inference(cnf_transformation,[],[f25])).
% 1.93/0.64  fof(f25,plain,(
% 1.93/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.93/0.64    inference(ennf_transformation,[],[f10])).
% 1.93/0.64  fof(f10,axiom,(
% 1.93/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.93/0.64  fof(f327,plain,(
% 1.93/0.64    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_2),
% 1.93/0.64    inference(backward_demodulation,[],[f294,f202])).
% 1.93/0.64  fof(f294,plain,(
% 1.93/0.64    r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_2),
% 1.93/0.64    inference(backward_demodulation,[],[f76,f201])).
% 1.93/0.64  fof(f76,plain,(
% 1.93/0.64    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl4_2),
% 1.93/0.64    inference(avatar_component_clause,[],[f75])).
% 1.93/0.64  fof(f157,plain,(
% 1.93/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_xboole_0(X1,X0)) | r1_tarski(k4_xboole_0(X2,X0),X1)) )),
% 1.93/0.64    inference(superposition,[],[f62,f46])).
% 1.93/0.64  fof(f46,plain,(
% 1.93/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.93/0.64    inference(cnf_transformation,[],[f1])).
% 1.93/0.64  fof(f1,axiom,(
% 1.93/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.93/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.93/0.64  fof(f79,plain,(
% 1.93/0.64    spl4_1 | spl4_2),
% 1.93/0.64    inference(avatar_split_clause,[],[f40,f75,f71])).
% 1.93/0.64  fof(f40,plain,(
% 1.93/0.64    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 1.93/0.64    inference(cnf_transformation,[],[f30])).
% 1.93/0.64  fof(f78,plain,(
% 1.93/0.64    ~spl4_1 | ~spl4_2),
% 1.93/0.64    inference(avatar_split_clause,[],[f41,f75,f71])).
% 1.93/0.64  fof(f41,plain,(
% 1.93/0.64    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 1.93/0.64    inference(cnf_transformation,[],[f30])).
% 1.93/0.64  % SZS output end Proof for theBenchmark
% 1.93/0.64  % (2113)------------------------------
% 1.93/0.64  % (2113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.64  % (2113)Termination reason: Refutation
% 1.93/0.64  
% 1.93/0.64  % (2113)Memory used [KB]: 11129
% 1.93/0.64  % (2113)Time elapsed: 0.139 s
% 1.93/0.64  % (2113)------------------------------
% 1.93/0.64  % (2113)------------------------------
% 1.93/0.64  % (2106)Success in time 0.283 s
%------------------------------------------------------------------------------
