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
% DateTime   : Thu Dec  3 12:45:00 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 212 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   21
%              Number of atoms          :  231 ( 680 expanded)
%              Number of equality atoms :   27 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2653,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f158,f1795,f2652])).

fof(f2652,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f2651])).

fof(f2651,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f2650,f436])).

fof(f436,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0)
    | spl4_1 ),
    inference(resolution,[],[f249,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f249,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f244,f56])).

fof(f56,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f244,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(resolution,[],[f187,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f187,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f186,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f186,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f182,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f182,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(superposition,[],[f99,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f99,plain,
    ( ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_1
  <=> m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2650,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f2642,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2642,plain,(
    r1_tarski(k2_xboole_0(sK2,sK1),sK0) ),
    inference(superposition,[],[f2154,f106])).

fof(f106,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f85,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f85,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f75,f59])).

fof(f59,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f71,f56])).

fof(f71,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2154,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f1995,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1995,plain,(
    ! [X22] : r1_tarski(k4_xboole_0(k2_xboole_0(X22,sK1),X22),sK0) ),
    inference(resolution,[],[f1502,f84])).

fof(f84,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | r1_tarski(X2,sK0) ) ),
    inference(resolution,[],[f76,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f76,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f67,f59])).

fof(f67,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f63,f56])).

fof(f63,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f36,f52])).

fof(f1502,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(k2_xboole_0(X8,X9),X8),X9) ),
    inference(resolution,[],[f1468,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1468,plain,(
    ! [X2] : r1_tarski(X2,X2) ),
    inference(superposition,[],[f49,f1125])).

fof(f1125,plain,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(sK1,sK0)) = X1 ),
    inference(superposition,[],[f269,f57])).

fof(f269,plain,(
    ! [X1] : k2_xboole_0(k4_xboole_0(sK1,sK0),X1) = X1 ),
    inference(resolution,[],[f256,f47])).

fof(f256,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,sK0),X0) ),
    inference(resolution,[],[f254,f41])).

fof(f254,plain,(
    ! [X5] : r1_tarski(sK1,k2_xboole_0(sK0,X5)) ),
    inference(resolution,[],[f83,f49])).

fof(f83,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,X1)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f76,f39])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1795,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f1794])).

fof(f1794,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f1789,f49])).

fof(f1789,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | spl4_5 ),
    inference(resolution,[],[f1764,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f1764,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl4_5 ),
    inference(forward_demodulation,[],[f157,f337])).

fof(f337,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f60,f37])).

fof(f60,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k2_xboole_0(sK1,X0) = k4_subset_1(sK0,sK1,X0) ) ),
    inference(resolution,[],[f36,f51])).

fof(f157,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl4_5
  <=> r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f158,plain,
    ( ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f151,f155,f97])).

fof(f151,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f125,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f125,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f38,f62])).

fof(f62,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f36,f50])).

fof(f38,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (816283648)
% 0.21/0.38  ipcrm: permission denied for id (816414731)
% 0.21/0.38  ipcrm: permission denied for id (816447501)
% 0.21/0.39  ipcrm: permission denied for id (816513040)
% 0.21/0.40  ipcrm: permission denied for id (816807963)
% 0.21/0.40  ipcrm: permission denied for id (816840732)
% 0.21/0.40  ipcrm: permission denied for id (816906270)
% 0.21/0.41  ipcrm: permission denied for id (816971810)
% 0.21/0.41  ipcrm: permission denied for id (817135655)
% 0.21/0.42  ipcrm: permission denied for id (817168427)
% 0.21/0.42  ipcrm: permission denied for id (817201196)
% 0.21/0.43  ipcrm: permission denied for id (817332272)
% 0.21/0.43  ipcrm: permission denied for id (817397811)
% 0.21/0.43  ipcrm: permission denied for id (817463349)
% 0.21/0.43  ipcrm: permission denied for id (817528887)
% 0.21/0.44  ipcrm: permission denied for id (817659966)
% 0.21/0.45  ipcrm: permission denied for id (817725506)
% 0.21/0.45  ipcrm: permission denied for id (817758277)
% 0.21/0.45  ipcrm: permission denied for id (817791046)
% 0.21/0.45  ipcrm: permission denied for id (817823815)
% 0.21/0.46  ipcrm: permission denied for id (817856584)
% 0.21/0.46  ipcrm: permission denied for id (817922124)
% 0.21/0.47  ipcrm: permission denied for id (817954898)
% 0.21/0.47  ipcrm: permission denied for id (818020438)
% 0.21/0.47  ipcrm: permission denied for id (818053207)
% 0.21/0.48  ipcrm: permission denied for id (818085977)
% 0.21/0.48  ipcrm: permission denied for id (818184286)
% 0.21/0.48  ipcrm: permission denied for id (818217055)
% 0.21/0.48  ipcrm: permission denied for id (818249824)
% 0.21/0.49  ipcrm: permission denied for id (818315364)
% 0.21/0.49  ipcrm: permission denied for id (818348133)
% 0.21/0.49  ipcrm: permission denied for id (818380902)
% 0.21/0.49  ipcrm: permission denied for id (818446440)
% 0.21/0.50  ipcrm: permission denied for id (818479210)
% 0.21/0.51  ipcrm: permission denied for id (818675826)
% 0.21/0.51  ipcrm: permission denied for id (818774135)
% 0.21/0.52  ipcrm: permission denied for id (818872443)
% 0.21/0.52  ipcrm: permission denied for id (818905212)
% 0.59/0.63  % (28741)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.59/0.63  % (28746)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.09/0.64  % (28754)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.09/0.64  % (28738)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.09/0.65  % (28749)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.26/0.66  % (28753)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.26/0.66  % (28756)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.26/0.66  % (28748)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.67  % (28736)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.26/0.67  % (28743)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.26/0.67  % (28750)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.26/0.67  % (28755)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.26/0.67  % (28739)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.67  % (28740)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.26/0.67  % (28737)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.68  % (28742)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.26/0.68  % (28751)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.26/0.68  % (28747)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.26/0.68  % (28744)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.26/0.68  % (28745)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.26/0.69  % (28752)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.97/0.77  % (28755)Refutation found. Thanks to Tanya!
% 1.97/0.77  % SZS status Theorem for theBenchmark
% 1.97/0.77  % SZS output start Proof for theBenchmark
% 1.97/0.77  fof(f2653,plain,(
% 1.97/0.77    $false),
% 1.97/0.77    inference(avatar_sat_refutation,[],[f158,f1795,f2652])).
% 1.97/0.77  fof(f2652,plain,(
% 1.97/0.77    spl4_1),
% 1.97/0.77    inference(avatar_contradiction_clause,[],[f2651])).
% 1.97/0.77  fof(f2651,plain,(
% 1.97/0.77    $false | spl4_1),
% 1.97/0.77    inference(subsumption_resolution,[],[f2650,f436])).
% 1.97/0.77  fof(f436,plain,(
% 1.97/0.77    ~r1_tarski(k2_xboole_0(sK1,sK2),sK0) | spl4_1),
% 1.97/0.77    inference(resolution,[],[f249,f58])).
% 1.97/0.77  fof(f58,plain,(
% 1.97/0.77    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.97/0.77    inference(equality_resolution,[],[f44])).
% 1.97/0.77  fof(f44,plain,(
% 1.97/0.77    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.97/0.77    inference(cnf_transformation,[],[f34])).
% 1.97/0.77  fof(f34,plain,(
% 1.97/0.77    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.97/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 1.97/0.77  fof(f33,plain,(
% 1.97/0.77    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.97/0.77    introduced(choice_axiom,[])).
% 1.97/0.77  fof(f32,plain,(
% 1.97/0.77    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.97/0.77    inference(rectify,[],[f31])).
% 1.97/0.77  fof(f31,plain,(
% 1.97/0.77    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.97/0.77    inference(nnf_transformation,[],[f10])).
% 1.97/0.77  fof(f10,axiom,(
% 1.97/0.77    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.97/0.77  fof(f249,plain,(
% 1.97/0.77    ~r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl4_1),
% 1.97/0.77    inference(subsumption_resolution,[],[f244,f56])).
% 1.97/0.77  fof(f56,plain,(
% 1.97/0.77    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.97/0.77    inference(cnf_transformation,[],[f13])).
% 1.97/0.77  fof(f13,axiom,(
% 1.97/0.77    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.97/0.77  fof(f244,plain,(
% 1.97/0.77    ~r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | spl4_1),
% 1.97/0.77    inference(resolution,[],[f187,f53])).
% 1.97/0.77  fof(f53,plain,(
% 1.97/0.77    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.97/0.77    inference(cnf_transformation,[],[f35])).
% 1.97/0.77  fof(f35,plain,(
% 1.97/0.77    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.97/0.77    inference(nnf_transformation,[],[f27])).
% 1.97/0.77  fof(f27,plain,(
% 1.97/0.77    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.97/0.77    inference(ennf_transformation,[],[f11])).
% 1.97/0.77  fof(f11,axiom,(
% 1.97/0.77    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.97/0.77  fof(f187,plain,(
% 1.97/0.77    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl4_1),
% 1.97/0.77    inference(subsumption_resolution,[],[f186,f36])).
% 1.97/0.77  fof(f36,plain,(
% 1.97/0.77    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.97/0.77    inference(cnf_transformation,[],[f30])).
% 1.97/0.77  fof(f30,plain,(
% 1.97/0.77    (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.97/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f29,f28])).
% 1.97/0.77  fof(f28,plain,(
% 1.97/0.77    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.97/0.77    introduced(choice_axiom,[])).
% 1.97/0.77  fof(f29,plain,(
% 1.97/0.77    ? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.97/0.77    introduced(choice_axiom,[])).
% 1.97/0.77  fof(f17,plain,(
% 1.97/0.77    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.97/0.77    inference(ennf_transformation,[],[f16])).
% 1.97/0.77  fof(f16,negated_conjecture,(
% 1.97/0.77    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 1.97/0.77    inference(negated_conjecture,[],[f15])).
% 1.97/0.77  fof(f15,conjecture,(
% 1.97/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 1.97/0.77  fof(f186,plain,(
% 1.97/0.77    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_1),
% 1.97/0.77    inference(subsumption_resolution,[],[f182,f37])).
% 1.97/0.77  fof(f37,plain,(
% 1.97/0.77    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.97/0.77    inference(cnf_transformation,[],[f30])).
% 1.97/0.77  fof(f182,plain,(
% 1.97/0.77    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_1),
% 1.97/0.77    inference(superposition,[],[f99,f51])).
% 1.97/0.77  fof(f51,plain,(
% 1.97/0.77    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.97/0.77    inference(cnf_transformation,[],[f26])).
% 1.97/0.77  fof(f26,plain,(
% 1.97/0.77    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.97/0.77    inference(flattening,[],[f25])).
% 1.97/0.77  fof(f25,plain,(
% 1.97/0.77    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.97/0.77    inference(ennf_transformation,[],[f14])).
% 1.97/0.77  fof(f14,axiom,(
% 1.97/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.97/0.77  fof(f99,plain,(
% 1.97/0.77    ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | spl4_1),
% 1.97/0.77    inference(avatar_component_clause,[],[f97])).
% 1.97/0.77  fof(f97,plain,(
% 1.97/0.77    spl4_1 <=> m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.97/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.97/0.77  fof(f2650,plain,(
% 1.97/0.77    r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 1.97/0.77    inference(forward_demodulation,[],[f2642,f57])).
% 1.97/0.77  fof(f57,plain,(
% 1.97/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.97/0.77    inference(cnf_transformation,[],[f1])).
% 1.97/0.77  fof(f1,axiom,(
% 1.97/0.77    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.97/0.77  fof(f2642,plain,(
% 1.97/0.77    r1_tarski(k2_xboole_0(sK2,sK1),sK0)),
% 1.97/0.77    inference(superposition,[],[f2154,f106])).
% 1.97/0.77  fof(f106,plain,(
% 1.97/0.77    sK0 = k2_xboole_0(sK2,sK0)),
% 1.97/0.77    inference(resolution,[],[f85,f47])).
% 1.97/0.77  fof(f47,plain,(
% 1.97/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.97/0.77    inference(cnf_transformation,[],[f23])).
% 1.97/0.77  fof(f23,plain,(
% 1.97/0.77    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.97/0.77    inference(ennf_transformation,[],[f2])).
% 1.97/0.77  fof(f2,axiom,(
% 1.97/0.77    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.97/0.77  fof(f85,plain,(
% 1.97/0.77    r1_tarski(sK2,sK0)),
% 1.97/0.77    inference(resolution,[],[f75,f59])).
% 1.97/0.77  fof(f59,plain,(
% 1.97/0.77    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.97/0.77    inference(equality_resolution,[],[f43])).
% 1.97/0.77  fof(f43,plain,(
% 1.97/0.77    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.97/0.77    inference(cnf_transformation,[],[f34])).
% 1.97/0.77  fof(f75,plain,(
% 1.97/0.77    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.97/0.77    inference(subsumption_resolution,[],[f71,f56])).
% 1.97/0.77  fof(f71,plain,(
% 1.97/0.77    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.97/0.77    inference(resolution,[],[f37,f52])).
% 1.97/0.77  fof(f52,plain,(
% 1.97/0.77    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.97/0.77    inference(cnf_transformation,[],[f35])).
% 1.97/0.77  fof(f2154,plain,(
% 1.97/0.77    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0))) )),
% 1.97/0.77    inference(resolution,[],[f1995,f40])).
% 1.97/0.77  fof(f40,plain,(
% 1.97/0.77    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.97/0.77    inference(cnf_transformation,[],[f20])).
% 1.97/0.77  fof(f20,plain,(
% 1.97/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.97/0.77    inference(ennf_transformation,[],[f8])).
% 1.97/0.77  fof(f8,axiom,(
% 1.97/0.77    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.97/0.77  fof(f1995,plain,(
% 1.97/0.77    ( ! [X22] : (r1_tarski(k4_xboole_0(k2_xboole_0(X22,sK1),X22),sK0)) )),
% 1.97/0.77    inference(resolution,[],[f1502,f84])).
% 1.97/0.77  fof(f84,plain,(
% 1.97/0.77    ( ! [X2] : (~r1_tarski(X2,sK1) | r1_tarski(X2,sK0)) )),
% 1.97/0.77    inference(resolution,[],[f76,f39])).
% 1.97/0.77  fof(f39,plain,(
% 1.97/0.77    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.97/0.77    inference(cnf_transformation,[],[f19])).
% 1.97/0.77  fof(f19,plain,(
% 1.97/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.97/0.77    inference(flattening,[],[f18])).
% 1.97/0.77  fof(f18,plain,(
% 1.97/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.97/0.77    inference(ennf_transformation,[],[f4])).
% 1.97/0.77  fof(f4,axiom,(
% 1.97/0.77    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.97/0.77  fof(f76,plain,(
% 1.97/0.77    r1_tarski(sK1,sK0)),
% 1.97/0.77    inference(resolution,[],[f67,f59])).
% 1.97/0.77  fof(f67,plain,(
% 1.97/0.77    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.97/0.77    inference(subsumption_resolution,[],[f63,f56])).
% 1.97/0.77  fof(f63,plain,(
% 1.97/0.77    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.97/0.77    inference(resolution,[],[f36,f52])).
% 1.97/0.77  fof(f1502,plain,(
% 1.97/0.77    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(k2_xboole_0(X8,X9),X8),X9)) )),
% 1.97/0.77    inference(resolution,[],[f1468,f41])).
% 1.97/0.77  fof(f41,plain,(
% 1.97/0.77    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.97/0.77    inference(cnf_transformation,[],[f21])).
% 1.97/0.77  fof(f21,plain,(
% 1.97/0.77    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.97/0.77    inference(ennf_transformation,[],[f7])).
% 1.97/0.77  fof(f7,axiom,(
% 1.97/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.97/0.77  fof(f1468,plain,(
% 1.97/0.77    ( ! [X2] : (r1_tarski(X2,X2)) )),
% 1.97/0.77    inference(superposition,[],[f49,f1125])).
% 1.97/0.77  fof(f1125,plain,(
% 1.97/0.77    ( ! [X1] : (k2_xboole_0(X1,k4_xboole_0(sK1,sK0)) = X1) )),
% 1.97/0.77    inference(superposition,[],[f269,f57])).
% 1.97/0.77  fof(f269,plain,(
% 1.97/0.77    ( ! [X1] : (k2_xboole_0(k4_xboole_0(sK1,sK0),X1) = X1) )),
% 1.97/0.77    inference(resolution,[],[f256,f47])).
% 1.97/0.77  fof(f256,plain,(
% 1.97/0.77    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,sK0),X0)) )),
% 1.97/0.77    inference(resolution,[],[f254,f41])).
% 1.97/0.77  fof(f254,plain,(
% 1.97/0.77    ( ! [X5] : (r1_tarski(sK1,k2_xboole_0(sK0,X5))) )),
% 1.97/0.77    inference(resolution,[],[f83,f49])).
% 1.97/0.77  fof(f83,plain,(
% 1.97/0.77    ( ! [X1] : (~r1_tarski(sK0,X1) | r1_tarski(sK1,X1)) )),
% 1.97/0.77    inference(resolution,[],[f76,f39])).
% 1.97/0.77  fof(f49,plain,(
% 1.97/0.77    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.97/0.77    inference(cnf_transformation,[],[f9])).
% 1.97/0.77  fof(f9,axiom,(
% 1.97/0.77    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.97/0.77  fof(f1795,plain,(
% 1.97/0.77    spl4_5),
% 1.97/0.77    inference(avatar_contradiction_clause,[],[f1794])).
% 1.97/0.77  fof(f1794,plain,(
% 1.97/0.77    $false | spl4_5),
% 1.97/0.77    inference(subsumption_resolution,[],[f1789,f49])).
% 1.97/0.77  fof(f1789,plain,(
% 1.97/0.77    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | spl4_5),
% 1.97/0.77    inference(resolution,[],[f1764,f42])).
% 1.97/0.77  fof(f42,plain,(
% 1.97/0.77    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 1.97/0.77    inference(cnf_transformation,[],[f22])).
% 1.97/0.77  fof(f22,plain,(
% 1.97/0.77    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.97/0.77    inference(ennf_transformation,[],[f5])).
% 1.97/0.77  fof(f5,axiom,(
% 1.97/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.97/0.77  fof(f1764,plain,(
% 1.97/0.77    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | spl4_5),
% 1.97/0.77    inference(forward_demodulation,[],[f157,f337])).
% 1.97/0.77  fof(f337,plain,(
% 1.97/0.77    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 1.97/0.77    inference(resolution,[],[f60,f37])).
% 1.97/0.77  fof(f60,plain,(
% 1.97/0.77    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_xboole_0(sK1,X0) = k4_subset_1(sK0,sK1,X0)) )),
% 1.97/0.77    inference(resolution,[],[f36,f51])).
% 1.97/0.77  fof(f157,plain,(
% 1.97/0.77    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | spl4_5),
% 1.97/0.77    inference(avatar_component_clause,[],[f155])).
% 1.97/0.77  fof(f155,plain,(
% 1.97/0.77    spl4_5 <=> r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 1.97/0.77    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.97/0.77  fof(f158,plain,(
% 1.97/0.77    ~spl4_1 | ~spl4_5),
% 1.97/0.77    inference(avatar_split_clause,[],[f151,f155,f97])).
% 1.97/0.77  fof(f151,plain,(
% 1.97/0.77    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.97/0.77    inference(superposition,[],[f125,f50])).
% 1.97/0.77  fof(f50,plain,(
% 1.97/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.97/0.77    inference(cnf_transformation,[],[f24])).
% 1.97/0.77  fof(f24,plain,(
% 1.97/0.77    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.97/0.77    inference(ennf_transformation,[],[f12])).
% 1.97/0.77  fof(f12,axiom,(
% 1.97/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.97/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.97/0.77  fof(f125,plain,(
% 1.97/0.77    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 1.97/0.77    inference(backward_demodulation,[],[f38,f62])).
% 1.97/0.77  fof(f62,plain,(
% 1.97/0.77    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.97/0.77    inference(resolution,[],[f36,f50])).
% 1.97/0.77  fof(f38,plain,(
% 1.97/0.77    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 1.97/0.77    inference(cnf_transformation,[],[f30])).
% 1.97/0.77  % SZS output end Proof for theBenchmark
% 1.97/0.77  % (28755)------------------------------
% 1.97/0.77  % (28755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.77  % (28755)Termination reason: Refutation
% 1.97/0.77  
% 1.97/0.77  % (28755)Memory used [KB]: 7036
% 1.97/0.77  % (28755)Time elapsed: 0.191 s
% 1.97/0.77  % (28755)------------------------------
% 1.97/0.77  % (28755)------------------------------
% 1.97/0.78  % (28565)Success in time 0.416 s
%------------------------------------------------------------------------------
