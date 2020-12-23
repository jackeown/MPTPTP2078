%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:00 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
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
fof(f2770,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f1694,f2769])).

fof(f2769,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f2768])).

fof(f2768,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f2767,f449])).

fof(f449,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0)
    | spl4_1 ),
    inference(resolution,[],[f248,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
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

fof(f248,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f243,f57])).

fof(f57,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f243,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(resolution,[],[f189,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f189,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f188,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f188,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f184,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f184,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(superposition,[],[f101,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f101,plain,
    ( ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_1
  <=> m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2767,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f2760,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2760,plain,(
    r1_tarski(k2_xboole_0(sK2,sK1),sK0) ),
    inference(superposition,[],[f2256,f108])).

fof(f108,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f87,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f87,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f77,f61])).

fof(f61,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f73,f57])).

fof(f73,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f38,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2256,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f1999,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1999,plain,(
    ! [X22] : r1_tarski(k4_xboole_0(k2_xboole_0(X22,sK1),X22),sK0) ),
    inference(resolution,[],[f1568,f86])).

fof(f86,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | r1_tarski(X2,sK0) ) ),
    inference(resolution,[],[f78,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f78,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f69,f61])).

fof(f69,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f65,f57])).

fof(f65,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f37,f53])).

fof(f1568,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(k2_xboole_0(X8,X9),X8),X9) ),
    inference(resolution,[],[f1542,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1542,plain,(
    ! [X2] : r1_tarski(X2,X2) ),
    inference(superposition,[],[f50,f1188])).

fof(f1188,plain,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(sK1,sK0)) = X1 ),
    inference(superposition,[],[f268,f58])).

fof(f268,plain,(
    ! [X1] : k2_xboole_0(k4_xboole_0(sK1,sK0),X1) = X1 ),
    inference(resolution,[],[f254,f48])).

fof(f254,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,sK0),X0) ),
    inference(resolution,[],[f253,f42])).

fof(f253,plain,(
    ! [X5] : r1_tarski(sK1,k2_xboole_0(sK0,X5)) ),
    inference(resolution,[],[f85,f50])).

fof(f85,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,X1)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f78,f40])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1694,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f1693])).

fof(f1693,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f1688,f50])).

fof(f1688,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | spl4_5 ),
    inference(resolution,[],[f1669,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f1669,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl4_5 ),
    inference(forward_demodulation,[],[f159,f348])).

fof(f348,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f62,f38])).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k2_xboole_0(sK1,X0) = k4_subset_1(sK0,sK1,X0) ) ),
    inference(resolution,[],[f37,f52])).

fof(f159,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_5
  <=> r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f160,plain,
    ( ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f153,f157,f99])).

fof(f153,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f127,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f127,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f39,f64])).

fof(f64,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f37,f51])).

fof(f39,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:33:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (11347)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  % (11340)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (11357)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.48  % (11354)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (11341)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (11352)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (11359)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (11342)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (11339)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (11345)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (11356)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (11348)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (11349)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (11353)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (11350)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (11351)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (11344)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (11358)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (11343)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (11355)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (11346)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.83/0.62  % (11358)Refutation found. Thanks to Tanya!
% 1.83/0.62  % SZS status Theorem for theBenchmark
% 1.83/0.62  % SZS output start Proof for theBenchmark
% 1.83/0.62  fof(f2770,plain,(
% 1.83/0.62    $false),
% 1.83/0.62    inference(avatar_sat_refutation,[],[f160,f1694,f2769])).
% 1.83/0.62  fof(f2769,plain,(
% 1.83/0.62    spl4_1),
% 1.83/0.62    inference(avatar_contradiction_clause,[],[f2768])).
% 1.83/0.62  fof(f2768,plain,(
% 1.83/0.62    $false | spl4_1),
% 1.83/0.62    inference(subsumption_resolution,[],[f2767,f449])).
% 1.83/0.62  fof(f449,plain,(
% 1.83/0.62    ~r1_tarski(k2_xboole_0(sK1,sK2),sK0) | spl4_1),
% 1.83/0.62    inference(resolution,[],[f248,f60])).
% 1.83/0.62  fof(f60,plain,(
% 1.83/0.62    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.83/0.62    inference(equality_resolution,[],[f45])).
% 1.83/0.62  fof(f45,plain,(
% 1.83/0.62    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.83/0.62    inference(cnf_transformation,[],[f35])).
% 1.83/0.62  fof(f35,plain,(
% 1.83/0.62    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.83/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 1.83/0.62  fof(f34,plain,(
% 1.83/0.62    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.83/0.62    introduced(choice_axiom,[])).
% 1.83/0.62  fof(f33,plain,(
% 1.83/0.62    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.83/0.62    inference(rectify,[],[f32])).
% 1.83/0.62  fof(f32,plain,(
% 1.83/0.62    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.83/0.62    inference(nnf_transformation,[],[f10])).
% 1.83/0.62  fof(f10,axiom,(
% 1.83/0.62    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.83/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.83/0.62  fof(f248,plain,(
% 1.83/0.62    ~r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl4_1),
% 1.83/0.62    inference(subsumption_resolution,[],[f243,f57])).
% 1.83/0.62  fof(f57,plain,(
% 1.83/0.62    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.83/0.62    inference(cnf_transformation,[],[f13])).
% 1.83/0.62  fof(f13,axiom,(
% 1.83/0.62    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.83/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.83/0.62  fof(f243,plain,(
% 1.83/0.62    ~r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | spl4_1),
% 1.83/0.62    inference(resolution,[],[f189,f54])).
% 1.83/0.62  fof(f54,plain,(
% 1.83/0.62    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f36])).
% 1.83/0.62  fof(f36,plain,(
% 1.83/0.62    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.83/0.62    inference(nnf_transformation,[],[f28])).
% 1.83/0.62  fof(f28,plain,(
% 1.83/0.62    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.83/0.62    inference(ennf_transformation,[],[f11])).
% 1.83/0.62  fof(f11,axiom,(
% 1.83/0.62    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.83/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.83/0.62  fof(f189,plain,(
% 1.83/0.62    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl4_1),
% 1.83/0.62    inference(subsumption_resolution,[],[f188,f37])).
% 1.83/0.62  fof(f37,plain,(
% 1.83/0.62    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.83/0.62    inference(cnf_transformation,[],[f31])).
% 1.83/0.62  fof(f31,plain,(
% 1.83/0.62    (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.83/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f30,f29])).
% 1.83/0.62  fof(f29,plain,(
% 1.83/0.62    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.83/0.62    introduced(choice_axiom,[])).
% 1.83/0.62  fof(f30,plain,(
% 1.83/0.62    ? [X2] : (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.83/0.62    introduced(choice_axiom,[])).
% 1.83/0.62  fof(f18,plain,(
% 1.83/0.62    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.83/0.62    inference(ennf_transformation,[],[f16])).
% 1.83/0.62  fof(f16,negated_conjecture,(
% 1.83/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 1.83/0.62    inference(negated_conjecture,[],[f15])).
% 1.83/0.62  fof(f15,conjecture,(
% 1.83/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 1.83/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 1.83/0.62  fof(f188,plain,(
% 1.83/0.62    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_1),
% 1.83/0.62    inference(subsumption_resolution,[],[f184,f38])).
% 1.83/0.62  fof(f38,plain,(
% 1.83/0.62    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.83/0.62    inference(cnf_transformation,[],[f31])).
% 1.83/0.62  fof(f184,plain,(
% 1.83/0.62    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_1),
% 1.83/0.62    inference(superposition,[],[f101,f52])).
% 1.83/0.62  fof(f52,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.83/0.62    inference(cnf_transformation,[],[f27])).
% 1.83/0.62  fof(f27,plain,(
% 1.83/0.62    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.83/0.62    inference(flattening,[],[f26])).
% 1.83/0.62  fof(f26,plain,(
% 1.83/0.62    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.83/0.62    inference(ennf_transformation,[],[f14])).
% 1.83/0.62  fof(f14,axiom,(
% 1.83/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.83/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.83/0.62  fof(f101,plain,(
% 1.83/0.62    ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | spl4_1),
% 1.83/0.62    inference(avatar_component_clause,[],[f99])).
% 1.83/0.62  fof(f99,plain,(
% 1.83/0.62    spl4_1 <=> m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.83/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.83/0.62  fof(f2767,plain,(
% 1.83/0.62    r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 1.83/0.62    inference(forward_demodulation,[],[f2760,f58])).
% 1.83/0.62  fof(f58,plain,(
% 1.83/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f1])).
% 1.83/0.62  fof(f1,axiom,(
% 1.83/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.83/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.83/0.64  fof(f2760,plain,(
% 1.83/0.64    r1_tarski(k2_xboole_0(sK2,sK1),sK0)),
% 1.83/0.64    inference(superposition,[],[f2256,f108])).
% 1.83/0.64  fof(f108,plain,(
% 1.83/0.64    sK0 = k2_xboole_0(sK2,sK0)),
% 1.83/0.64    inference(resolution,[],[f87,f48])).
% 1.83/0.64  fof(f48,plain,(
% 1.83/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f24])).
% 1.83/0.64  fof(f24,plain,(
% 1.83/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.83/0.64    inference(ennf_transformation,[],[f3])).
% 1.83/0.64  fof(f3,axiom,(
% 1.83/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.83/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.83/0.64  fof(f87,plain,(
% 1.83/0.64    r1_tarski(sK2,sK0)),
% 1.83/0.64    inference(resolution,[],[f77,f61])).
% 1.83/0.64  fof(f61,plain,(
% 1.83/0.64    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.83/0.64    inference(equality_resolution,[],[f44])).
% 1.83/0.64  fof(f44,plain,(
% 1.83/0.64    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.83/0.64    inference(cnf_transformation,[],[f35])).
% 1.83/0.64  fof(f77,plain,(
% 1.83/0.64    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.83/0.64    inference(subsumption_resolution,[],[f73,f57])).
% 1.83/0.64  fof(f73,plain,(
% 1.83/0.64    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.83/0.64    inference(resolution,[],[f38,f53])).
% 1.83/0.64  fof(f53,plain,(
% 1.83/0.64    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f36])).
% 1.83/0.64  fof(f2256,plain,(
% 1.83/0.64    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0))) )),
% 1.83/0.64    inference(resolution,[],[f1999,f41])).
% 1.83/0.64  fof(f41,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f21])).
% 1.83/0.64  fof(f21,plain,(
% 1.83/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.83/0.64    inference(ennf_transformation,[],[f8])).
% 1.83/0.64  fof(f8,axiom,(
% 1.83/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.83/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.83/0.64  fof(f1999,plain,(
% 1.83/0.64    ( ! [X22] : (r1_tarski(k4_xboole_0(k2_xboole_0(X22,sK1),X22),sK0)) )),
% 1.83/0.64    inference(resolution,[],[f1568,f86])).
% 1.83/0.64  fof(f86,plain,(
% 1.83/0.64    ( ! [X2] : (~r1_tarski(X2,sK1) | r1_tarski(X2,sK0)) )),
% 1.83/0.64    inference(resolution,[],[f78,f40])).
% 1.83/0.64  fof(f40,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f20])).
% 1.83/0.64  fof(f20,plain,(
% 1.83/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.83/0.64    inference(flattening,[],[f19])).
% 1.83/0.64  fof(f19,plain,(
% 1.83/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.83/0.64    inference(ennf_transformation,[],[f4])).
% 1.83/0.64  fof(f4,axiom,(
% 1.83/0.64    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.83/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.83/0.64  fof(f78,plain,(
% 1.83/0.64    r1_tarski(sK1,sK0)),
% 1.83/0.64    inference(resolution,[],[f69,f61])).
% 1.83/0.64  fof(f69,plain,(
% 1.83/0.64    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.83/0.64    inference(subsumption_resolution,[],[f65,f57])).
% 1.83/0.64  fof(f65,plain,(
% 1.83/0.64    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.83/0.64    inference(resolution,[],[f37,f53])).
% 1.83/0.64  fof(f1568,plain,(
% 1.83/0.64    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(k2_xboole_0(X8,X9),X8),X9)) )),
% 1.83/0.64    inference(resolution,[],[f1542,f42])).
% 1.83/0.64  fof(f42,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.83/0.64    inference(cnf_transformation,[],[f22])).
% 1.83/0.64  fof(f22,plain,(
% 1.83/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.83/0.64    inference(ennf_transformation,[],[f7])).
% 1.83/0.64  fof(f7,axiom,(
% 1.83/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.83/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.83/0.64  fof(f1542,plain,(
% 1.83/0.64    ( ! [X2] : (r1_tarski(X2,X2)) )),
% 1.83/0.64    inference(superposition,[],[f50,f1188])).
% 1.83/0.64  fof(f1188,plain,(
% 1.83/0.64    ( ! [X1] : (k2_xboole_0(X1,k4_xboole_0(sK1,sK0)) = X1) )),
% 1.83/0.64    inference(superposition,[],[f268,f58])).
% 1.83/0.64  fof(f268,plain,(
% 1.83/0.64    ( ! [X1] : (k2_xboole_0(k4_xboole_0(sK1,sK0),X1) = X1) )),
% 1.83/0.64    inference(resolution,[],[f254,f48])).
% 1.83/0.64  fof(f254,plain,(
% 1.83/0.64    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,sK0),X0)) )),
% 1.83/0.64    inference(resolution,[],[f253,f42])).
% 1.83/0.64  fof(f253,plain,(
% 1.83/0.64    ( ! [X5] : (r1_tarski(sK1,k2_xboole_0(sK0,X5))) )),
% 1.83/0.64    inference(resolution,[],[f85,f50])).
% 1.83/0.64  fof(f85,plain,(
% 1.83/0.64    ( ! [X1] : (~r1_tarski(sK0,X1) | r1_tarski(sK1,X1)) )),
% 1.83/0.64    inference(resolution,[],[f78,f40])).
% 1.83/0.64  fof(f50,plain,(
% 1.83/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.83/0.64    inference(cnf_transformation,[],[f9])).
% 1.83/0.64  fof(f9,axiom,(
% 1.83/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.83/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.83/0.64  fof(f1694,plain,(
% 1.83/0.64    spl4_5),
% 1.83/0.64    inference(avatar_contradiction_clause,[],[f1693])).
% 1.83/0.64  fof(f1693,plain,(
% 1.83/0.64    $false | spl4_5),
% 1.83/0.64    inference(subsumption_resolution,[],[f1688,f50])).
% 1.83/0.64  fof(f1688,plain,(
% 1.83/0.64    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | spl4_5),
% 1.83/0.64    inference(resolution,[],[f1669,f43])).
% 1.83/0.64  fof(f43,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f23])).
% 1.83/0.64  fof(f23,plain,(
% 1.83/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.83/0.64    inference(ennf_transformation,[],[f5])).
% 1.83/0.64  fof(f5,axiom,(
% 1.83/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.83/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.83/0.64  fof(f1669,plain,(
% 1.83/0.64    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | spl4_5),
% 1.83/0.64    inference(forward_demodulation,[],[f159,f348])).
% 1.83/0.64  fof(f348,plain,(
% 1.83/0.64    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 1.83/0.64    inference(resolution,[],[f62,f38])).
% 1.83/0.64  fof(f62,plain,(
% 1.83/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_xboole_0(sK1,X0) = k4_subset_1(sK0,sK1,X0)) )),
% 1.83/0.64    inference(resolution,[],[f37,f52])).
% 1.83/0.64  fof(f159,plain,(
% 1.83/0.64    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | spl4_5),
% 1.83/0.64    inference(avatar_component_clause,[],[f157])).
% 1.83/0.64  fof(f157,plain,(
% 1.83/0.64    spl4_5 <=> r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 1.83/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.83/0.64  fof(f160,plain,(
% 1.83/0.64    ~spl4_1 | ~spl4_5),
% 1.83/0.64    inference(avatar_split_clause,[],[f153,f157,f99])).
% 1.83/0.64  fof(f153,plain,(
% 1.83/0.64    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.83/0.64    inference(superposition,[],[f127,f51])).
% 1.83/0.64  fof(f51,plain,(
% 1.83/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.83/0.64    inference(cnf_transformation,[],[f25])).
% 1.83/0.64  fof(f25,plain,(
% 1.83/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.83/0.64    inference(ennf_transformation,[],[f12])).
% 1.83/0.64  fof(f12,axiom,(
% 1.83/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.83/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.83/0.64  fof(f127,plain,(
% 1.83/0.64    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 1.83/0.64    inference(backward_demodulation,[],[f39,f64])).
% 1.83/0.64  fof(f64,plain,(
% 1.83/0.64    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.83/0.64    inference(resolution,[],[f37,f51])).
% 1.83/0.64  fof(f39,plain,(
% 1.83/0.64    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 1.83/0.64    inference(cnf_transformation,[],[f31])).
% 1.83/0.64  % SZS output end Proof for theBenchmark
% 1.83/0.64  % (11358)------------------------------
% 1.83/0.64  % (11358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.64  % (11358)Termination reason: Refutation
% 1.83/0.64  
% 1.83/0.64  % (11358)Memory used [KB]: 7036
% 1.83/0.64  % (11358)Time elapsed: 0.202 s
% 1.83/0.64  % (11358)------------------------------
% 1.83/0.64  % (11358)------------------------------
% 1.83/0.64  % (11338)Success in time 0.279 s
%------------------------------------------------------------------------------
