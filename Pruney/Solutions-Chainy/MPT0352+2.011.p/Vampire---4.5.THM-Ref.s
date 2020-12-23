%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:15 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 182 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   20
%              Number of atoms          :  266 ( 639 expanded)
%              Number of equality atoms :   33 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f81,f1358,f1397])).

fof(f1397,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f1396])).

fof(f1396,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f1395,f74])).

fof(f74,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1395,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_2 ),
    inference(resolution,[],[f1369,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f1369,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(forward_demodulation,[],[f1368,f208])).

fof(f208,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f55,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1368,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(forward_demodulation,[],[f79,f207])).

fof(f207,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f55,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_2
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1358,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f1357])).

fof(f1357,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f1356,f75])).

fof(f75,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f1356,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f1355,f104])).

fof(f104,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f54,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1355,plain,
    ( r1_tarski(sK1,k2_xboole_0(k1_xboole_0,sK2))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f1354,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1354,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f1353,f347])).

fof(f347,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f134,f193])).

fof(f193,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,sK0),X0) ),
    inference(resolution,[],[f191,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f191,plain,(
    ! [X0] : r1_tarski(sK1,k2_xboole_0(sK0,X0)) ),
    inference(resolution,[],[f119,f45])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f119,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f65,f110])).

fof(f110,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f54,f96])).

fof(f96,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f94,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f94,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f91,f43])).

fof(f43,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f91,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f50,f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f58,f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1353,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f1337,f48])).

fof(f1337,plain,
    ( r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f215,f1093])).

fof(f1093,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f179,f315])).

fof(f315,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(resolution,[],[f314,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f314,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f302,f208])).

fof(f302,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f78,f207])).

fof(f78,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_xboole_0(X1,X0))
      | r1_tarski(k4_xboole_0(X2,X0),X1) ) ),
    inference(superposition,[],[f64,f48])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)
      | r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ) ),
    inference(superposition,[],[f66,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f47,f49,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f81,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f41,f77,f73])).

fof(f41,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f42,f77,f73])).

fof(f42,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (8560)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (8552)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (8568)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (8556)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (8549)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (8555)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (8550)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (8544)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (8567)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (8560)Refutation not found, incomplete strategy% (8560)------------------------------
% 0.22/0.53  % (8560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8560)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8560)Memory used [KB]: 10618
% 0.22/0.53  % (8560)Time elapsed: 0.107 s
% 0.22/0.53  % (8560)------------------------------
% 0.22/0.53  % (8560)------------------------------
% 0.22/0.53  % (8559)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (8546)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (8547)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (8548)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (8569)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (8573)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (8558)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (8570)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (8562)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (8572)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (8565)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (8572)Refutation not found, incomplete strategy% (8572)------------------------------
% 0.22/0.55  % (8572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8572)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8572)Memory used [KB]: 10874
% 0.22/0.55  % (8572)Time elapsed: 0.143 s
% 0.22/0.55  % (8572)------------------------------
% 0.22/0.55  % (8572)------------------------------
% 0.22/0.55  % (8551)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (8571)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (8554)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (8564)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (8554)Refutation not found, incomplete strategy% (8554)------------------------------
% 0.22/0.56  % (8554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8554)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8554)Memory used [KB]: 10874
% 0.22/0.56  % (8554)Time elapsed: 0.151 s
% 0.22/0.56  % (8554)------------------------------
% 0.22/0.56  % (8554)------------------------------
% 0.22/0.56  % (8557)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (8566)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (8563)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (8545)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.85/0.61  % (8553)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.85/0.61  % (8561)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.85/0.63  % (8550)Refutation found. Thanks to Tanya!
% 1.85/0.63  % SZS status Theorem for theBenchmark
% 1.85/0.63  % SZS output start Proof for theBenchmark
% 1.85/0.63  fof(f1398,plain,(
% 1.85/0.63    $false),
% 1.85/0.63    inference(avatar_sat_refutation,[],[f80,f81,f1358,f1397])).
% 1.85/0.63  fof(f1397,plain,(
% 1.85/0.63    ~spl4_1 | spl4_2),
% 1.85/0.63    inference(avatar_contradiction_clause,[],[f1396])).
% 1.85/0.63  fof(f1396,plain,(
% 1.85/0.63    $false | (~spl4_1 | spl4_2)),
% 1.85/0.63    inference(subsumption_resolution,[],[f1395,f74])).
% 1.85/0.63  fof(f74,plain,(
% 1.85/0.63    r1_tarski(sK1,sK2) | ~spl4_1),
% 1.85/0.63    inference(avatar_component_clause,[],[f73])).
% 1.85/0.63  fof(f73,plain,(
% 1.85/0.63    spl4_1 <=> r1_tarski(sK1,sK2)),
% 1.85/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.85/0.63  fof(f1395,plain,(
% 1.85/0.63    ~r1_tarski(sK1,sK2) | spl4_2),
% 1.85/0.63    inference(resolution,[],[f1369,f63])).
% 1.85/0.63  fof(f63,plain,(
% 1.85/0.63    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f23])).
% 1.85/0.63  fof(f23,plain,(
% 1.85/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.85/0.63    inference(ennf_transformation,[],[f7])).
% 1.85/0.63  fof(f7,axiom,(
% 1.85/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.85/0.63  fof(f1369,plain,(
% 1.85/0.63    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl4_2),
% 1.85/0.63    inference(forward_demodulation,[],[f1368,f208])).
% 1.85/0.63  fof(f208,plain,(
% 1.85/0.63    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.85/0.63    inference(resolution,[],[f55,f40])).
% 1.85/0.63  fof(f40,plain,(
% 1.85/0.63    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.85/0.63    inference(cnf_transformation,[],[f31])).
% 1.85/0.63  fof(f31,plain,(
% 1.85/0.63    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.85/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30,f29])).
% 1.85/0.63  fof(f29,plain,(
% 1.85/0.63    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.85/0.63    introduced(choice_axiom,[])).
% 1.85/0.63  fof(f30,plain,(
% 1.85/0.63    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.85/0.63    introduced(choice_axiom,[])).
% 1.85/0.63  fof(f28,plain,(
% 1.85/0.63    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.85/0.63    inference(flattening,[],[f27])).
% 1.85/0.63  fof(f27,plain,(
% 1.85/0.63    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.85/0.63    inference(nnf_transformation,[],[f19])).
% 1.85/0.63  fof(f19,plain,(
% 1.85/0.63    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.85/0.63    inference(ennf_transformation,[],[f18])).
% 1.85/0.63  fof(f18,negated_conjecture,(
% 1.85/0.63    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.85/0.63    inference(negated_conjecture,[],[f17])).
% 1.85/0.63  fof(f17,conjecture,(
% 1.85/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 1.85/0.63  fof(f55,plain,(
% 1.85/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f22])).
% 1.85/0.63  fof(f22,plain,(
% 1.85/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.85/0.63    inference(ennf_transformation,[],[f15])).
% 1.85/0.63  fof(f15,axiom,(
% 1.85/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.85/0.63  fof(f1368,plain,(
% 1.85/0.63    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl4_2),
% 1.85/0.63    inference(forward_demodulation,[],[f79,f207])).
% 1.85/0.63  fof(f207,plain,(
% 1.85/0.63    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.85/0.63    inference(resolution,[],[f55,f39])).
% 1.85/0.63  fof(f39,plain,(
% 1.85/0.63    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.85/0.63    inference(cnf_transformation,[],[f31])).
% 1.85/0.63  fof(f79,plain,(
% 1.85/0.63    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl4_2),
% 1.85/0.63    inference(avatar_component_clause,[],[f77])).
% 1.85/0.63  fof(f77,plain,(
% 1.85/0.63    spl4_2 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 1.85/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.85/0.63  fof(f1358,plain,(
% 1.85/0.63    spl4_1 | ~spl4_2),
% 1.85/0.63    inference(avatar_contradiction_clause,[],[f1357])).
% 1.85/0.63  fof(f1357,plain,(
% 1.85/0.63    $false | (spl4_1 | ~spl4_2)),
% 1.85/0.63    inference(subsumption_resolution,[],[f1356,f75])).
% 1.85/0.63  fof(f75,plain,(
% 1.85/0.63    ~r1_tarski(sK1,sK2) | spl4_1),
% 1.85/0.63    inference(avatar_component_clause,[],[f73])).
% 1.85/0.63  fof(f1356,plain,(
% 1.85/0.63    r1_tarski(sK1,sK2) | ~spl4_2),
% 1.85/0.63    inference(forward_demodulation,[],[f1355,f104])).
% 1.85/0.63  fof(f104,plain,(
% 1.85/0.63    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.85/0.63    inference(resolution,[],[f54,f44])).
% 1.85/0.63  fof(f44,plain,(
% 1.85/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f6])).
% 1.85/0.63  fof(f6,axiom,(
% 1.85/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.85/0.63  fof(f54,plain,(
% 1.85/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.85/0.63    inference(cnf_transformation,[],[f21])).
% 1.85/0.63  fof(f21,plain,(
% 1.85/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.85/0.63    inference(ennf_transformation,[],[f5])).
% 1.85/0.63  fof(f5,axiom,(
% 1.85/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.85/0.63  fof(f1355,plain,(
% 1.85/0.63    r1_tarski(sK1,k2_xboole_0(k1_xboole_0,sK2)) | ~spl4_2),
% 1.85/0.63    inference(forward_demodulation,[],[f1354,f48])).
% 1.85/0.63  fof(f48,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f1])).
% 1.85/0.63  fof(f1,axiom,(
% 1.85/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.85/0.63  fof(f1354,plain,(
% 1.85/0.63    r1_tarski(sK1,k2_xboole_0(sK2,k1_xboole_0)) | ~spl4_2),
% 1.85/0.63    inference(forward_demodulation,[],[f1353,f347])).
% 1.85/0.63  fof(f347,plain,(
% 1.85/0.63    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.85/0.63    inference(resolution,[],[f134,f193])).
% 1.85/0.63  fof(f193,plain,(
% 1.85/0.63    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,sK0),X0)) )),
% 1.85/0.63    inference(resolution,[],[f191,f64])).
% 1.85/0.63  fof(f64,plain,(
% 1.85/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f24])).
% 1.85/0.63  fof(f24,plain,(
% 1.85/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.85/0.63    inference(ennf_transformation,[],[f9])).
% 1.85/0.63  fof(f9,axiom,(
% 1.85/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.85/0.63  fof(f191,plain,(
% 1.85/0.63    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(sK0,X0))) )),
% 1.85/0.63    inference(resolution,[],[f119,f45])).
% 1.85/0.63  fof(f45,plain,(
% 1.85/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f12])).
% 1.85/0.63  fof(f12,axiom,(
% 1.85/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.85/0.63  fof(f119,plain,(
% 1.85/0.63    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(sK1,X0)) )),
% 1.85/0.63    inference(superposition,[],[f65,f110])).
% 1.85/0.63  fof(f110,plain,(
% 1.85/0.63    sK0 = k2_xboole_0(sK1,sK0)),
% 1.85/0.63    inference(resolution,[],[f54,f96])).
% 1.85/0.63  fof(f96,plain,(
% 1.85/0.63    r1_tarski(sK1,sK0)),
% 1.85/0.63    inference(resolution,[],[f94,f71])).
% 1.85/0.63  fof(f71,plain,(
% 1.85/0.63    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.85/0.63    inference(equality_resolution,[],[f59])).
% 1.85/0.63  fof(f59,plain,(
% 1.85/0.63    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.85/0.63    inference(cnf_transformation,[],[f38])).
% 1.85/0.63  fof(f38,plain,(
% 1.85/0.63    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.85/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.85/0.63  fof(f37,plain,(
% 1.85/0.63    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.85/0.63    introduced(choice_axiom,[])).
% 1.85/0.63  fof(f36,plain,(
% 1.85/0.63    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.85/0.63    inference(rectify,[],[f35])).
% 1.85/0.63  fof(f35,plain,(
% 1.85/0.63    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.85/0.63    inference(nnf_transformation,[],[f13])).
% 1.85/0.63  fof(f13,axiom,(
% 1.85/0.63    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.85/0.63  fof(f94,plain,(
% 1.85/0.63    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.85/0.63    inference(subsumption_resolution,[],[f91,f43])).
% 1.85/0.63  fof(f43,plain,(
% 1.85/0.63    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f16])).
% 1.85/0.63  fof(f16,axiom,(
% 1.85/0.63    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.85/0.63  fof(f91,plain,(
% 1.85/0.63    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.85/0.63    inference(resolution,[],[f50,f39])).
% 1.85/0.63  fof(f50,plain,(
% 1.85/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f32])).
% 1.85/0.63  fof(f32,plain,(
% 1.85/0.63    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.85/0.63    inference(nnf_transformation,[],[f20])).
% 1.85/0.63  fof(f20,plain,(
% 1.85/0.63    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.85/0.63    inference(ennf_transformation,[],[f14])).
% 1.85/0.63  fof(f14,axiom,(
% 1.85/0.63    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.85/0.63  fof(f65,plain,(
% 1.85/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f25])).
% 1.85/0.63  fof(f25,plain,(
% 1.85/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.85/0.63    inference(ennf_transformation,[],[f4])).
% 1.85/0.63  fof(f4,axiom,(
% 1.85/0.63    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.85/0.63  fof(f134,plain,(
% 1.85/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.85/0.63    inference(resolution,[],[f58,f44])).
% 1.85/0.63  fof(f58,plain,(
% 1.85/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f34])).
% 1.85/0.63  fof(f34,plain,(
% 1.85/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.85/0.63    inference(flattening,[],[f33])).
% 1.85/0.63  fof(f33,plain,(
% 1.85/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.85/0.63    inference(nnf_transformation,[],[f3])).
% 1.85/0.63  fof(f3,axiom,(
% 1.85/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.85/0.63  fof(f1353,plain,(
% 1.85/0.63    r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))) | ~spl4_2),
% 1.85/0.63    inference(forward_demodulation,[],[f1337,f48])).
% 1.85/0.63  fof(f1337,plain,(
% 1.85/0.63    r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),sK2)) | ~spl4_2),
% 1.85/0.63    inference(resolution,[],[f215,f1093])).
% 1.85/0.63  fof(f1093,plain,(
% 1.85/0.63    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) | ~spl4_2),
% 1.85/0.63    inference(resolution,[],[f179,f315])).
% 1.85/0.63  fof(f315,plain,(
% 1.85/0.63    r1_tarski(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl4_2),
% 1.85/0.63    inference(resolution,[],[f314,f66])).
% 1.85/0.63  fof(f66,plain,(
% 1.85/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f26])).
% 1.85/0.63  fof(f26,plain,(
% 1.85/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.85/0.63    inference(ennf_transformation,[],[f10])).
% 1.85/0.63  fof(f10,axiom,(
% 1.85/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.85/0.63  fof(f314,plain,(
% 1.85/0.63    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_2),
% 1.85/0.63    inference(backward_demodulation,[],[f302,f208])).
% 1.85/0.63  fof(f302,plain,(
% 1.85/0.63    r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_2),
% 1.85/0.63    inference(backward_demodulation,[],[f78,f207])).
% 1.85/0.63  fof(f78,plain,(
% 1.85/0.63    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl4_2),
% 1.85/0.63    inference(avatar_component_clause,[],[f77])).
% 1.85/0.63  fof(f179,plain,(
% 1.85/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_xboole_0(X1,X0)) | r1_tarski(k4_xboole_0(X2,X0),X1)) )),
% 1.85/0.63    inference(superposition,[],[f64,f48])).
% 1.85/0.63  fof(f215,plain,(
% 1.85/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) | r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 1.85/0.63    inference(superposition,[],[f66,f67])).
% 1.85/0.63  fof(f67,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.85/0.63    inference(definition_unfolding,[],[f47,f49,f49])).
% 1.85/0.63  fof(f49,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.85/0.63    inference(cnf_transformation,[],[f11])).
% 1.85/0.63  fof(f11,axiom,(
% 1.85/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.85/0.63  fof(f47,plain,(
% 1.85/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.85/0.63    inference(cnf_transformation,[],[f2])).
% 1.85/0.63  fof(f2,axiom,(
% 1.85/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.85/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.85/0.63  fof(f81,plain,(
% 1.85/0.63    spl4_1 | spl4_2),
% 1.85/0.63    inference(avatar_split_clause,[],[f41,f77,f73])).
% 1.85/0.63  fof(f41,plain,(
% 1.85/0.63    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 1.85/0.63    inference(cnf_transformation,[],[f31])).
% 1.85/0.63  fof(f80,plain,(
% 1.85/0.63    ~spl4_1 | ~spl4_2),
% 1.85/0.63    inference(avatar_split_clause,[],[f42,f77,f73])).
% 1.85/0.63  fof(f42,plain,(
% 1.85/0.63    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 1.85/0.63    inference(cnf_transformation,[],[f31])).
% 1.85/0.63  % SZS output end Proof for theBenchmark
% 1.85/0.63  % (8550)------------------------------
% 1.85/0.63  % (8550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.63  % (8550)Termination reason: Refutation
% 1.85/0.63  
% 1.85/0.63  % (8550)Memory used [KB]: 11641
% 1.85/0.63  % (8550)Time elapsed: 0.203 s
% 1.85/0.63  % (8550)------------------------------
% 1.85/0.63  % (8550)------------------------------
% 1.85/0.63  % (8543)Success in time 0.267 s
%------------------------------------------------------------------------------
