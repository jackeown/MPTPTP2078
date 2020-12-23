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
% DateTime   : Thu Dec  3 12:45:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 176 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  240 ( 566 expanded)
%              Number of equality atoms :   21 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f791,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f702,f720,f790])).

fof(f790,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f789])).

fof(f789,plain,
    ( $false
    | spl4_17 ),
    inference(subsumption_resolution,[],[f788,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27])).

fof(f27,plain,
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

fof(f28,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f788,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_17 ),
    inference(subsumption_resolution,[],[f787,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f787,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_17 ),
    inference(subsumption_resolution,[],[f786,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f786,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_17 ),
    inference(superposition,[],[f773,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f773,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))
    | spl4_17 ),
    inference(subsumption_resolution,[],[f758,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f40,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f758,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))
    | ~ r1_tarski(sK0,sK0)
    | spl4_17 ),
    inference(resolution,[],[f719,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).

fof(f719,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f718])).

fof(f718,plain,
    ( spl4_17
  <=> r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f720,plain,
    ( ~ spl4_1
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f121,f718,f90])).

fof(f90,plain,
    ( spl4_1
  <=> m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f121,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f96,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f96,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f88,f35])).

fof(f88,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f37,f46])).

fof(f37,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f702,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f701])).

fof(f701,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f698,f71])).

fof(f71,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f67,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f67,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f64,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f41,f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f698,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_1 ),
    inference(resolution,[],[f404,f140])).

fof(f140,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0)
    | spl4_1 ),
    inference(resolution,[],[f70,f112])).

fof(f112,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f111,f35])).

fof(f111,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f110,f36])).

fof(f110,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(superposition,[],[f91,f54])).

fof(f91,plain,
    ( ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f69,f38])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f404,plain,(
    ! [X0] :
      ( r1_tarski(k2_xboole_0(X0,sK2),sK0)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(superposition,[],[f343,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f343,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f242,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f242,plain,(
    ! [X17] : r1_tarski(k4_xboole_0(k2_xboole_0(X17,sK2),X17),sK0) ),
    inference(resolution,[],[f80,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f85,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f85,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f68,f57])).

fof(f68,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f65,f38])).

fof(f65,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f41,f36])).

fof(f80,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(k2_xboole_0(X2,X3),X2),X3) ),
    inference(resolution,[],[f51,f58])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:13:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (6584)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.45  % (6592)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.46  % (6597)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.46  % (6599)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.47  % (6582)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.47  % (6595)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.47  % (6594)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.47  % (6585)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.47  % (6587)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.48  % (6589)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.48  % (6583)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.48  % (6586)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.48  % (6588)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.49  % (6590)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.49  % (6591)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.49  % (6602)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.49  % (6598)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.49  % (6602)Refutation not found, incomplete strategy% (6602)------------------------------
% 0.19/0.49  % (6602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (6602)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (6602)Memory used [KB]: 10618
% 0.19/0.49  % (6602)Time elapsed: 0.100 s
% 0.19/0.49  % (6602)------------------------------
% 0.19/0.49  % (6602)------------------------------
% 0.19/0.49  % (6593)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.50  % (6596)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.50  % (6601)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.50  % (6600)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.52  % (6584)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f791,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f702,f720,f790])).
% 0.19/0.52  fof(f790,plain,(
% 0.19/0.52    spl4_17),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f789])).
% 0.19/0.52  fof(f789,plain,(
% 0.19/0.52    $false | spl4_17),
% 0.19/0.52    inference(subsumption_resolution,[],[f788,f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.19/0.52    inference(negated_conjecture,[],[f13])).
% 0.19/0.52  fof(f13,conjecture,(
% 0.19/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 0.19/0.52  fof(f788,plain,(
% 0.19/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_17),
% 0.19/0.52    inference(subsumption_resolution,[],[f787,f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f787,plain,(
% 0.19/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_17),
% 0.19/0.52    inference(subsumption_resolution,[],[f786,f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.52  fof(f786,plain,(
% 0.19/0.52    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_17),
% 0.19/0.52    inference(superposition,[],[f773,f54])).
% 0.19/0.52  fof(f54,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.52    inference(flattening,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.19/0.52    inference(ennf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.19/0.52  fof(f773,plain,(
% 0.19/0.52    ~r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) | spl4_17),
% 0.19/0.52    inference(subsumption_resolution,[],[f758,f58])).
% 0.19/0.52  fof(f58,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.19/0.52    inference(superposition,[],[f40,f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.19/0.52  fof(f758,plain,(
% 0.19/0.52    ~r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) | ~r1_tarski(sK0,sK0) | spl4_17),
% 0.19/0.52    inference(resolution,[],[f719,f55])).
% 0.19/0.52  fof(f55,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.19/0.52    inference(flattening,[],[f25])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).
% 0.19/0.52  fof(f719,plain,(
% 0.19/0.52    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | spl4_17),
% 0.19/0.52    inference(avatar_component_clause,[],[f718])).
% 0.19/0.52  fof(f718,plain,(
% 0.19/0.52    spl4_17 <=> r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.19/0.52  fof(f720,plain,(
% 0.19/0.52    ~spl4_1 | ~spl4_17),
% 0.19/0.52    inference(avatar_split_clause,[],[f121,f718,f90])).
% 0.19/0.52  fof(f90,plain,(
% 0.19/0.52    spl4_1 <=> m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.52  fof(f121,plain,(
% 0.19/0.52    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(superposition,[],[f96,f46])).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f18])).
% 0.19/0.52  fof(f18,plain,(
% 0.19/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,axiom,(
% 0.19/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.52  fof(f96,plain,(
% 0.19/0.52    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 0.19/0.52    inference(subsumption_resolution,[],[f88,f35])).
% 0.19/0.52  fof(f88,plain,(
% 0.19/0.52    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(superposition,[],[f37,f46])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f702,plain,(
% 0.19/0.52    spl4_1),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f701])).
% 0.19/0.52  fof(f701,plain,(
% 0.19/0.52    $false | spl4_1),
% 0.19/0.52    inference(subsumption_resolution,[],[f698,f71])).
% 0.19/0.52  fof(f71,plain,(
% 0.19/0.52    r1_tarski(sK1,sK0)),
% 0.19/0.52    inference(resolution,[],[f67,f57])).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.19/0.52    inference(equality_resolution,[],[f47])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.52    inference(rectify,[],[f31])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.52    inference(nnf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,axiom,(
% 0.19/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.52  fof(f67,plain,(
% 0.19/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(subsumption_resolution,[],[f64,f38])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f11])).
% 0.19/0.52  fof(f11,axiom,(
% 0.19/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.19/0.52  fof(f64,plain,(
% 0.19/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(resolution,[],[f41,f35])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.19/0.52    inference(nnf_transformation,[],[f16])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f9])).
% 0.19/0.52  fof(f9,axiom,(
% 0.19/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.52  fof(f698,plain,(
% 0.19/0.52    ~r1_tarski(sK1,sK0) | spl4_1),
% 0.19/0.52    inference(resolution,[],[f404,f140])).
% 0.19/0.52  fof(f140,plain,(
% 0.19/0.52    ~r1_tarski(k2_xboole_0(sK1,sK2),sK0) | spl4_1),
% 0.19/0.52    inference(resolution,[],[f70,f112])).
% 0.19/0.52  fof(f112,plain,(
% 0.19/0.52    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl4_1),
% 0.19/0.52    inference(subsumption_resolution,[],[f111,f35])).
% 0.19/0.52  fof(f111,plain,(
% 0.19/0.52    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_1),
% 0.19/0.52    inference(subsumption_resolution,[],[f110,f36])).
% 0.19/0.52  fof(f110,plain,(
% 0.19/0.52    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_1),
% 0.19/0.52    inference(superposition,[],[f91,f54])).
% 0.19/0.52  fof(f91,plain,(
% 0.19/0.52    ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | spl4_1),
% 0.19/0.52    inference(avatar_component_clause,[],[f90])).
% 0.19/0.52  fof(f70,plain,(
% 0.19/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f69,f38])).
% 0.19/0.52  fof(f69,plain,(
% 0.19/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(resolution,[],[f42,f56])).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.19/0.52    inference(equality_resolution,[],[f48])).
% 0.19/0.52  fof(f48,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f34])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f30])).
% 0.19/0.52  fof(f404,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK2),sK0) | ~r1_tarski(X0,sK0)) )),
% 0.19/0.52    inference(superposition,[],[f343,f45])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f17])).
% 0.19/0.52  fof(f17,plain,(
% 0.19/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.52  fof(f343,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK2),k2_xboole_0(X0,sK0))) )),
% 0.19/0.52    inference(resolution,[],[f242,f52])).
% 0.19/0.52  fof(f52,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f20])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.19/0.52    inference(ennf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.19/0.52  fof(f242,plain,(
% 0.19/0.52    ( ! [X17] : (r1_tarski(k4_xboole_0(k2_xboole_0(X17,sK2),X17),sK0)) )),
% 0.19/0.52    inference(resolution,[],[f80,f99])).
% 0.19/0.52  fof(f99,plain,(
% 0.19/0.52    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,sK0)) )),
% 0.19/0.52    inference(resolution,[],[f85,f53])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.52    inference(flattening,[],[f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.52  fof(f85,plain,(
% 0.19/0.52    r1_tarski(sK2,sK0)),
% 0.19/0.52    inference(resolution,[],[f68,f57])).
% 0.19/0.52  fof(f68,plain,(
% 0.19/0.52    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(subsumption_resolution,[],[f65,f38])).
% 0.19/0.52  fof(f65,plain,(
% 0.19/0.52    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.19/0.52    inference(resolution,[],[f41,f36])).
% 0.19/0.52  fof(f80,plain,(
% 0.19/0.52    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(k2_xboole_0(X2,X3),X2),X3)) )),
% 0.19/0.52    inference(resolution,[],[f51,f58])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f19])).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.19/0.52    inference(ennf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (6584)------------------------------
% 0.19/0.52  % (6584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (6584)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (6584)Memory used [KB]: 11385
% 0.19/0.52  % (6584)Time elapsed: 0.117 s
% 0.19/0.52  % (6584)------------------------------
% 0.19/0.52  % (6584)------------------------------
% 0.19/0.53  % (6578)Success in time 0.185 s
%------------------------------------------------------------------------------
