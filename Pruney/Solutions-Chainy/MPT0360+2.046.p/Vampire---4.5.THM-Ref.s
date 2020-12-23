%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:54 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 140 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  209 ( 432 expanded)
%              Number of equality atoms :   25 (  77 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f698,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f346,f344,f485])).

fof(f485,plain,(
    ! [X4,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X4))
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f222,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f48,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f222,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f93,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_zfmisc_1(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f80,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f80,plain,(
    ! [X1] : r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f40,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f76,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f47,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f63,f62])).

fof(f62,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f44,f61])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f344,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f343,f39])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f27])).

fof(f27,plain,
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

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f343,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f342,f37])).

fof(f37,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f342,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f336])).

fof(f336,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f196,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f196,plain,(
    ! [X23] :
      ( r1_tarski(sK1,k3_subset_1(sK0,X23))
      | ~ m1_subset_1(X23,k1_zfmisc_1(sK0))
      | ~ r1_tarski(X23,sK2) ) ),
    inference(subsumption_resolution,[],[f190,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f190,plain,(
    ! [X23] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X23,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k3_subset_1(sK0,X23))
      | ~ r1_tarski(X23,sK2) ) ),
    inference(resolution,[],[f109,f38])).

fof(f38,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f109,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X5,k3_subset_1(X4,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
      | r1_tarski(X5,k3_subset_1(X4,X2))
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f54,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f346,plain,(
    r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f345,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f345,plain,
    ( r1_tarski(sK1,sK0)
    | ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f340,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f340,plain,
    ( r1_tarski(sK1,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(superposition,[],[f196,f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:20:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.50  % (1501)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.18/0.51  % (1510)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.18/0.52  % (1518)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.18/0.52  % (1506)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.18/0.52  % (1505)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.53  % (1500)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.53  % (1507)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.53  % (1498)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.54  % (1499)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.54  % (1525)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.54  % (1497)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.54  % (1514)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.54  % (1496)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.54  % (1517)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.54  % (1522)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.54  % (1512)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.54  % (1516)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.54  % (1513)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.55  % (1526)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.55  % (1523)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.55  % (1508)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.55  % (1504)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.55  % (1503)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.55  % (1521)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.55  % (1515)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.56  % (1524)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.56  % (1520)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.58  % (1519)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.34/0.58  % (1526)Refutation found. Thanks to Tanya!
% 1.34/0.58  % SZS status Theorem for theBenchmark
% 1.34/0.58  % SZS output start Proof for theBenchmark
% 1.34/0.58  fof(f698,plain,(
% 1.34/0.58    $false),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f346,f344,f485])).
% 1.34/0.58  fof(f485,plain,(
% 1.34/0.58    ( ! [X4,X3] : (m1_subset_1(X3,k1_zfmisc_1(X4)) | ~r1_tarski(X3,X4)) )),
% 1.34/0.58    inference(resolution,[],[f222,f81])).
% 1.34/0.58  fof(f81,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.34/0.58    inference(subsumption_resolution,[],[f48,f59])).
% 1.34/0.58  fof(f59,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f24])).
% 1.34/0.58  fof(f24,plain,(
% 1.34/0.58    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 1.34/0.58    inference(ennf_transformation,[],[f4])).
% 1.34/0.58  fof(f4,axiom,(
% 1.34/0.58    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 1.34/0.58  fof(f48,plain,(
% 1.34/0.58    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f29])).
% 1.34/0.58  fof(f29,plain,(
% 1.34/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.34/0.58    inference(nnf_transformation,[],[f19])).
% 1.34/0.58  fof(f19,plain,(
% 1.34/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.34/0.58    inference(ennf_transformation,[],[f6])).
% 1.34/0.58  fof(f6,axiom,(
% 1.34/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.34/0.58  fof(f222,plain,(
% 1.34/0.58    ( ! [X0,X1] : (r2_hidden(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.34/0.58    inference(resolution,[],[f93,f51])).
% 1.34/0.58  fof(f51,plain,(
% 1.34/0.58    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f20])).
% 1.34/0.58  fof(f20,plain,(
% 1.34/0.58    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.34/0.58    inference(ennf_transformation,[],[f5])).
% 1.34/0.58  fof(f5,axiom,(
% 1.34/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.34/0.58  fof(f93,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~r1_tarski(k1_zfmisc_1(X0),X1) | r2_hidden(X0,X1)) )),
% 1.34/0.58    inference(resolution,[],[f80,f56])).
% 1.34/0.58  fof(f56,plain,(
% 1.34/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f35])).
% 1.34/0.58  fof(f35,plain,(
% 1.34/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 1.34/0.58  fof(f34,plain,(
% 1.34/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.34/0.58    introduced(choice_axiom,[])).
% 1.34/0.58  fof(f33,plain,(
% 1.34/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.58    inference(rectify,[],[f32])).
% 1.34/0.58  fof(f32,plain,(
% 1.34/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.58    inference(nnf_transformation,[],[f23])).
% 1.34/0.58  fof(f23,plain,(
% 1.34/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.34/0.58    inference(ennf_transformation,[],[f1])).
% 1.34/0.58  fof(f1,axiom,(
% 1.34/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.58  fof(f80,plain,(
% 1.34/0.58    ( ! [X1] : (r2_hidden(X1,k1_zfmisc_1(X1))) )),
% 1.34/0.58    inference(subsumption_resolution,[],[f76,f40])).
% 1.34/0.58  fof(f40,plain,(
% 1.34/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f11])).
% 1.34/0.58  fof(f11,axiom,(
% 1.34/0.58    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.34/0.58  fof(f76,plain,(
% 1.34/0.58    ( ! [X1] : (r2_hidden(X1,k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1))) )),
% 1.34/0.58    inference(resolution,[],[f47,f68])).
% 1.34/0.58  fof(f68,plain,(
% 1.34/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.34/0.58    inference(forward_demodulation,[],[f63,f62])).
% 1.34/0.58  fof(f62,plain,(
% 1.34/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.34/0.58    inference(definition_unfolding,[],[f43,f61])).
% 1.34/0.58  fof(f61,plain,(
% 1.34/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.34/0.58    inference(definition_unfolding,[],[f46,f42])).
% 1.34/0.58  fof(f42,plain,(
% 1.34/0.58    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f7])).
% 1.34/0.58  fof(f7,axiom,(
% 1.34/0.58    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.34/0.58  fof(f46,plain,(
% 1.34/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f12])).
% 1.34/0.58  fof(f12,axiom,(
% 1.34/0.58    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.34/0.58  fof(f43,plain,(
% 1.34/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.34/0.58    inference(cnf_transformation,[],[f8])).
% 1.34/0.58  fof(f8,axiom,(
% 1.34/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.34/0.58  fof(f63,plain,(
% 1.34/0.58    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 1.34/0.58    inference(definition_unfolding,[],[f44,f61])).
% 1.34/0.58  fof(f44,plain,(
% 1.34/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f10])).
% 1.34/0.58  fof(f10,axiom,(
% 1.34/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.34/0.58  fof(f47,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f29])).
% 1.34/0.58  fof(f344,plain,(
% 1.34/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.34/0.58    inference(subsumption_resolution,[],[f343,f39])).
% 1.34/0.58  fof(f39,plain,(
% 1.34/0.58    k1_xboole_0 != sK1),
% 1.34/0.58    inference(cnf_transformation,[],[f28])).
% 1.34/0.58  fof(f28,plain,(
% 1.34/0.58    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.34/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f27])).
% 1.34/0.58  fof(f27,plain,(
% 1.34/0.58    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.34/0.58    introduced(choice_axiom,[])).
% 1.34/0.58  fof(f18,plain,(
% 1.34/0.58    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.34/0.58    inference(flattening,[],[f17])).
% 1.34/0.58  fof(f17,plain,(
% 1.34/0.58    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.34/0.58    inference(ennf_transformation,[],[f16])).
% 1.34/0.58  fof(f16,negated_conjecture,(
% 1.34/0.58    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.34/0.58    inference(negated_conjecture,[],[f15])).
% 1.34/0.58  fof(f15,conjecture,(
% 1.34/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 1.34/0.58  fof(f343,plain,(
% 1.34/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | k1_xboole_0 = sK1),
% 1.34/0.58    inference(subsumption_resolution,[],[f342,f37])).
% 1.34/0.58  fof(f37,plain,(
% 1.34/0.58    r1_tarski(sK1,sK2)),
% 1.34/0.58    inference(cnf_transformation,[],[f28])).
% 1.34/0.58  fof(f342,plain,(
% 1.34/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~r1_tarski(sK1,sK2) | k1_xboole_0 = sK1),
% 1.34/0.58    inference(duplicate_literal_removal,[],[f336])).
% 1.34/0.58  fof(f336,plain,(
% 1.34/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~r1_tarski(sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.34/0.58    inference(resolution,[],[f196,f66])).
% 1.34/0.58  fof(f66,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.34/0.58    inference(definition_unfolding,[],[f52,f42])).
% 1.34/0.58  fof(f52,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f30])).
% 1.34/0.58  fof(f30,plain,(
% 1.34/0.58    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.58    inference(nnf_transformation,[],[f21])).
% 1.34/0.58  fof(f21,plain,(
% 1.34/0.58    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.58    inference(ennf_transformation,[],[f14])).
% 1.34/0.58  fof(f14,axiom,(
% 1.34/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 1.34/0.58  fof(f196,plain,(
% 1.34/0.58    ( ! [X23] : (r1_tarski(sK1,k3_subset_1(sK0,X23)) | ~m1_subset_1(X23,k1_zfmisc_1(sK0)) | ~r1_tarski(X23,sK2)) )),
% 1.34/0.58    inference(subsumption_resolution,[],[f190,f36])).
% 1.34/0.58  fof(f36,plain,(
% 1.34/0.58    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.34/0.58    inference(cnf_transformation,[],[f28])).
% 1.34/0.58  fof(f190,plain,(
% 1.34/0.58    ( ! [X23] : (~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(X23,k1_zfmisc_1(sK0)) | r1_tarski(sK1,k3_subset_1(sK0,X23)) | ~r1_tarski(X23,sK2)) )),
% 1.34/0.58    inference(resolution,[],[f109,f38])).
% 1.34/0.58  fof(f38,plain,(
% 1.34/0.58    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.34/0.58    inference(cnf_transformation,[],[f28])).
% 1.34/0.58  fof(f109,plain,(
% 1.34/0.58    ( ! [X4,X2,X5,X3] : (~r1_tarski(X5,k3_subset_1(X4,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(X4)) | ~m1_subset_1(X2,k1_zfmisc_1(X4)) | r1_tarski(X5,k3_subset_1(X4,X2)) | ~r1_tarski(X2,X3)) )),
% 1.34/0.58    inference(resolution,[],[f54,f60])).
% 1.34/0.58  fof(f60,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f26])).
% 1.34/0.58  fof(f26,plain,(
% 1.34/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.34/0.58    inference(flattening,[],[f25])).
% 1.34/0.58  fof(f25,plain,(
% 1.34/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.34/0.58    inference(ennf_transformation,[],[f2])).
% 1.34/0.58  fof(f2,axiom,(
% 1.34/0.58    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.34/0.58  fof(f54,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f31])).
% 1.34/0.58  fof(f31,plain,(
% 1.34/0.58    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.58    inference(nnf_transformation,[],[f22])).
% 1.34/0.58  fof(f22,plain,(
% 1.34/0.58    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.58    inference(ennf_transformation,[],[f13])).
% 1.34/0.58  fof(f13,axiom,(
% 1.34/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 1.34/0.58  fof(f346,plain,(
% 1.34/0.58    r1_tarski(sK1,sK0)),
% 1.34/0.58    inference(subsumption_resolution,[],[f345,f41])).
% 1.34/0.58  fof(f41,plain,(
% 1.34/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f3])).
% 1.34/0.58  fof(f3,axiom,(
% 1.34/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.34/0.58  fof(f345,plain,(
% 1.34/0.58    r1_tarski(sK1,sK0) | ~r1_tarski(k1_xboole_0,sK2)),
% 1.34/0.58    inference(subsumption_resolution,[],[f340,f64])).
% 1.34/0.58  fof(f64,plain,(
% 1.34/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.34/0.58    inference(definition_unfolding,[],[f45,f42])).
% 1.34/0.58  fof(f45,plain,(
% 1.34/0.58    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f9])).
% 1.34/0.58  fof(f9,axiom,(
% 1.34/0.58    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 1.34/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 1.34/0.58  fof(f340,plain,(
% 1.34/0.58    r1_tarski(sK1,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | ~r1_tarski(k1_xboole_0,sK2)),
% 1.34/0.58    inference(superposition,[],[f196,f62])).
% 1.34/0.58  % SZS output end Proof for theBenchmark
% 1.34/0.58  % (1526)------------------------------
% 1.34/0.58  % (1526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.58  % (1526)Termination reason: Refutation
% 1.34/0.58  
% 1.34/0.58  % (1526)Memory used [KB]: 1918
% 1.34/0.58  % (1526)Time elapsed: 0.174 s
% 1.34/0.58  % (1526)------------------------------
% 1.34/0.58  % (1526)------------------------------
% 1.34/0.58  % (1494)Success in time 0.223 s
%------------------------------------------------------------------------------
