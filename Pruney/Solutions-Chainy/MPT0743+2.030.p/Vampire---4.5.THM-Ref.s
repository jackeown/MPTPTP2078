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
% DateTime   : Thu Dec  3 12:55:26 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 961 expanded)
%              Number of leaves         :   12 ( 213 expanded)
%              Depth                    :   20
%              Number of atoms          :  240 (2757 expanded)
%              Number of equality atoms :   21 ( 183 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(subsumption_resolution,[],[f281,f66])).

fof(f66,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) ),
    inference(resolution,[],[f54,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f54,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f28,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f281,plain,(
    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK0) ),
    inference(forward_demodulation,[],[f280,f215])).

fof(f215,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f214,f174])).

fof(f174,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f173,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f173,plain,
    ( r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f171,f45])).

fof(f171,plain,
    ( r2_hidden(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f169,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f169,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | r1_tarski(sK1,sK0)
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f168,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f168,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f167,f142])).

fof(f142,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f141,f26])).

fof(f26,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f141,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f140,f27])).

fof(f27,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f140,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f135,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f135,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f125,f26])).

fof(f125,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r1_tarski(X1,sK0)
      | ~ r1_ordinal1(X1,sK0) ) ),
    inference(resolution,[],[f34,f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f167,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f166,f27])).

fof(f166,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f110,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f110,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f109,f26])).

fof(f109,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f31,f52])).

fof(f52,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f25,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f214,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f212,f163])).

fof(f163,plain,(
    ! [X1] : ~ r2_hidden(X1,X1) ),
    inference(subsumption_resolution,[],[f161,f65])).

fof(f65,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),X0) ),
    inference(resolution,[],[f45,f60])).

fof(f60,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f161,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,X1)
      | r1_tarski(k1_tarski(X1),X1) ) ),
    inference(superposition,[],[f40,f156])).

fof(f156,plain,(
    ! [X0] : sK2(k1_tarski(X0),X0) = X0 ),
    inference(resolution,[],[f70,f65])).

fof(f70,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_tarski(X2),X3)
      | sK2(k1_tarski(X2),X3) = X2 ) ),
    inference(resolution,[],[f39,f58])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f212,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK0,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f207,f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0)
      | r1_tarski(sK0,sK1) ) ),
    inference(resolution,[],[f143,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f143,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f138,f128])).

fof(f128,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f124,f27])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(X0,sK1)
      | ~ r1_ordinal1(X0,sK1) ) ),
    inference(resolution,[],[f34,f26])).

fof(f138,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f135,f115])).

fof(f115,plain,
    ( r1_ordinal1(sK1,sK0)
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f111,f27])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,sK1)
      | r1_ordinal1(sK1,X0) ) ),
    inference(resolution,[],[f32,f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f207,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f203,f133])).

fof(f133,plain,
    ( r2_hidden(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f132,f27])).

fof(f132,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f131,f26])).

fof(f131,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f128,f31])).

fof(f203,plain,
    ( ~ r2_hidden(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f192,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f192,plain,
    ( r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f185,f53])).

fof(f53,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f24,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f185,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    inference(resolution,[],[f129,f27])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK1)
      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK1) ) ),
    inference(resolution,[],[f124,f55])).

fof(f280,plain,(
    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f250,f266])).

fof(f266,plain,(
    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK0) ),
    inference(forward_demodulation,[],[f265,f215])).

fof(f265,plain,(
    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f220,f163])).

fof(f220,plain,
    ( r2_hidden(sK0,sK0)
    | r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    inference(backward_demodulation,[],[f53,f215])).

fof(f250,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK0)
    | r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    inference(backward_demodulation,[],[f185,f215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:19:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.30/0.54  % (6917)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.54  % (6918)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.30/0.55  % (6933)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.55  % (6925)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.55  % (6934)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.56  % (6913)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.56  % (6926)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.56  % (6915)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.56  % (6924)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.57  % (6922)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.57  % (6917)Refutation found. Thanks to Tanya!
% 1.45/0.57  % SZS status Theorem for theBenchmark
% 1.45/0.57  % SZS output start Proof for theBenchmark
% 1.45/0.57  fof(f282,plain,(
% 1.45/0.57    $false),
% 1.45/0.57    inference(subsumption_resolution,[],[f281,f66])).
% 1.45/0.57  fof(f66,plain,(
% 1.45/0.57    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0)) )),
% 1.45/0.57    inference(resolution,[],[f54,f45])).
% 1.45/0.57  fof(f45,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f23])).
% 1.45/0.57  fof(f23,plain,(
% 1.45/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.45/0.57    inference(ennf_transformation,[],[f11])).
% 1.45/0.57  fof(f11,axiom,(
% 1.45/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.45/0.57  fof(f54,plain,(
% 1.45/0.57    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 1.45/0.57    inference(definition_unfolding,[],[f28,f29])).
% 1.45/0.57  fof(f29,plain,(
% 1.45/0.57    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.45/0.57    inference(cnf_transformation,[],[f6])).
% 1.45/0.57  fof(f6,axiom,(
% 1.45/0.57    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.45/0.57  fof(f28,plain,(
% 1.45/0.57    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.45/0.57    inference(cnf_transformation,[],[f8])).
% 1.45/0.57  fof(f8,axiom,(
% 1.45/0.57    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.45/0.57  fof(f281,plain,(
% 1.45/0.57    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK0)),
% 1.45/0.57    inference(forward_demodulation,[],[f280,f215])).
% 1.45/0.57  fof(f215,plain,(
% 1.45/0.57    sK0 = sK1),
% 1.45/0.57    inference(resolution,[],[f214,f174])).
% 1.45/0.57  fof(f174,plain,(
% 1.45/0.57    ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 1.45/0.57    inference(subsumption_resolution,[],[f173,f37])).
% 1.45/0.57  fof(f37,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.45/0.57    inference(cnf_transformation,[],[f3])).
% 1.45/0.57  fof(f3,axiom,(
% 1.45/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.45/0.57  fof(f173,plain,(
% 1.45/0.57    r1_tarski(sK1,sK0) | sK0 = sK1 | ~r1_tarski(sK0,sK1)),
% 1.45/0.57    inference(resolution,[],[f171,f45])).
% 1.45/0.57  fof(f171,plain,(
% 1.45/0.57    r2_hidden(sK1,sK0) | r1_tarski(sK1,sK0) | sK0 = sK1),
% 1.45/0.57    inference(resolution,[],[f169,f58])).
% 1.45/0.57  fof(f58,plain,(
% 1.45/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.45/0.57    inference(equality_resolution,[],[f42])).
% 1.45/0.57  fof(f42,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.45/0.57    inference(cnf_transformation,[],[f4])).
% 1.45/0.57  fof(f4,axiom,(
% 1.45/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.45/0.57  fof(f169,plain,(
% 1.45/0.57    r2_hidden(sK1,k1_tarski(sK0)) | r1_tarski(sK1,sK0) | r2_hidden(sK1,sK0)),
% 1.45/0.57    inference(resolution,[],[f168,f63])).
% 1.45/0.57  fof(f63,plain,(
% 1.45/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 1.45/0.57    inference(equality_resolution,[],[f49])).
% 1.45/0.57  fof(f49,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f2])).
% 1.45/0.57  fof(f2,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.45/0.57  fof(f168,plain,(
% 1.45/0.57    r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | r1_tarski(sK1,sK0)),
% 1.45/0.57    inference(resolution,[],[f167,f142])).
% 1.45/0.57  fof(f142,plain,(
% 1.45/0.57    r2_hidden(sK0,sK1) | r1_tarski(sK1,sK0)),
% 1.45/0.57    inference(subsumption_resolution,[],[f141,f26])).
% 1.45/0.57  fof(f26,plain,(
% 1.45/0.57    v3_ordinal1(sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f14])).
% 1.45/0.57  fof(f14,plain,(
% 1.45/0.57    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f13])).
% 1.45/0.57  fof(f13,negated_conjecture,(
% 1.45/0.57    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.45/0.57    inference(negated_conjecture,[],[f12])).
% 1.45/0.57  fof(f12,conjecture,(
% 1.45/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 1.45/0.57  fof(f141,plain,(
% 1.45/0.57    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1)),
% 1.45/0.57    inference(subsumption_resolution,[],[f140,f27])).
% 1.45/0.57  fof(f27,plain,(
% 1.45/0.57    v3_ordinal1(sK0)),
% 1.45/0.57    inference(cnf_transformation,[],[f14])).
% 1.45/0.57  fof(f140,plain,(
% 1.45/0.57    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1)),
% 1.45/0.57    inference(resolution,[],[f135,f31])).
% 1.45/0.57  fof(f31,plain,(
% 1.45/0.57    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f17])).
% 1.45/0.57  fof(f17,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.45/0.57    inference(flattening,[],[f16])).
% 1.45/0.57  fof(f16,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f9])).
% 1.45/0.57  fof(f9,axiom,(
% 1.45/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.45/0.57  fof(f135,plain,(
% 1.45/0.57    ~r1_ordinal1(sK1,sK0) | r1_tarski(sK1,sK0)),
% 1.45/0.57    inference(resolution,[],[f125,f26])).
% 1.45/0.57  fof(f125,plain,(
% 1.45/0.57    ( ! [X1] : (~v3_ordinal1(X1) | r1_tarski(X1,sK0) | ~r1_ordinal1(X1,sK0)) )),
% 1.45/0.57    inference(resolution,[],[f34,f27])).
% 1.45/0.57  fof(f34,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f21])).
% 1.45/0.57  fof(f21,plain,(
% 1.45/0.57    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.45/0.57    inference(flattening,[],[f20])).
% 1.45/0.57  fof(f20,plain,(
% 1.45/0.57    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f7])).
% 1.45/0.57  fof(f7,axiom,(
% 1.45/0.57    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.45/0.57  fof(f167,plain,(
% 1.45/0.57    ~r2_hidden(sK0,sK1) | r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 1.45/0.57    inference(subsumption_resolution,[],[f166,f27])).
% 1.45/0.57  fof(f166,plain,(
% 1.45/0.57    r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 1.45/0.57    inference(resolution,[],[f110,f55])).
% 1.45/0.57  fof(f55,plain,(
% 1.45/0.57    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 1.45/0.57    inference(definition_unfolding,[],[f30,f29])).
% 1.45/0.57  fof(f30,plain,(
% 1.45/0.57    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0))) )),
% 1.45/0.57    inference(cnf_transformation,[],[f15])).
% 1.45/0.57  fof(f15,plain,(
% 1.45/0.57    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f10])).
% 1.45/0.57  fof(f10,axiom,(
% 1.45/0.57    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 1.45/0.57  fof(f110,plain,(
% 1.45/0.57    ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | ~r2_hidden(sK0,sK1)),
% 1.45/0.57    inference(subsumption_resolution,[],[f109,f26])).
% 1.45/0.57  fof(f109,plain,(
% 1.45/0.57    ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | ~r2_hidden(sK0,sK1)),
% 1.45/0.57    inference(resolution,[],[f31,f52])).
% 1.45/0.57  fof(f52,plain,(
% 1.45/0.57    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 1.45/0.57    inference(definition_unfolding,[],[f25,f29])).
% 1.45/0.57  fof(f25,plain,(
% 1.45/0.57    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f14])).
% 1.45/0.57  fof(f214,plain,(
% 1.45/0.57    r1_tarski(sK0,sK1)),
% 1.45/0.57    inference(subsumption_resolution,[],[f212,f163])).
% 1.45/0.57  fof(f163,plain,(
% 1.45/0.57    ( ! [X1] : (~r2_hidden(X1,X1)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f161,f65])).
% 1.45/0.57  fof(f65,plain,(
% 1.45/0.57    ( ! [X0] : (~r1_tarski(k1_tarski(X0),X0)) )),
% 1.45/0.57    inference(resolution,[],[f45,f60])).
% 1.45/0.57  fof(f60,plain,(
% 1.45/0.57    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 1.45/0.57    inference(equality_resolution,[],[f59])).
% 1.45/0.57  fof(f59,plain,(
% 1.45/0.57    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 1.45/0.57    inference(equality_resolution,[],[f41])).
% 1.45/0.57  fof(f41,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.45/0.57    inference(cnf_transformation,[],[f4])).
% 1.45/0.57  fof(f161,plain,(
% 1.45/0.57    ( ! [X1] : (~r2_hidden(X1,X1) | r1_tarski(k1_tarski(X1),X1)) )),
% 1.45/0.57    inference(superposition,[],[f40,f156])).
% 1.45/0.57  fof(f156,plain,(
% 1.45/0.57    ( ! [X0] : (sK2(k1_tarski(X0),X0) = X0) )),
% 1.45/0.57    inference(resolution,[],[f70,f65])).
% 1.45/0.57  fof(f70,plain,(
% 1.45/0.57    ( ! [X2,X3] : (r1_tarski(k1_tarski(X2),X3) | sK2(k1_tarski(X2),X3) = X2) )),
% 1.45/0.57    inference(resolution,[],[f39,f58])).
% 1.45/0.57  fof(f39,plain,(
% 1.45/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f22])).
% 1.45/0.57  fof(f22,plain,(
% 1.45/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f1])).
% 1.45/0.57  fof(f1,axiom,(
% 1.45/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.45/0.57  fof(f40,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f22])).
% 1.45/0.57  fof(f212,plain,(
% 1.45/0.57    r1_tarski(sK0,sK1) | r2_hidden(sK0,sK0)),
% 1.45/0.57    inference(duplicate_literal_removal,[],[f210])).
% 1.45/0.57  fof(f210,plain,(
% 1.45/0.57    r1_tarski(sK0,sK1) | r2_hidden(sK0,sK0) | r1_tarski(sK0,sK1)),
% 1.45/0.57    inference(resolution,[],[f207,f145])).
% 1.45/0.57  fof(f145,plain,(
% 1.45/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0) | r1_tarski(sK0,sK1)) )),
% 1.45/0.57    inference(resolution,[],[f143,f38])).
% 1.45/0.57  fof(f38,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f22])).
% 1.45/0.57  fof(f143,plain,(
% 1.45/0.57    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1)),
% 1.45/0.57    inference(resolution,[],[f138,f128])).
% 1.45/0.57  fof(f128,plain,(
% 1.45/0.57    ~r1_ordinal1(sK0,sK1) | r1_tarski(sK0,sK1)),
% 1.45/0.57    inference(resolution,[],[f124,f27])).
% 1.45/0.57  fof(f124,plain,(
% 1.45/0.57    ( ! [X0] : (~v3_ordinal1(X0) | r1_tarski(X0,sK1) | ~r1_ordinal1(X0,sK1)) )),
% 1.45/0.57    inference(resolution,[],[f34,f26])).
% 1.45/0.57  fof(f138,plain,(
% 1.45/0.57    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0)),
% 1.45/0.57    inference(resolution,[],[f135,f115])).
% 1.45/0.57  fof(f115,plain,(
% 1.45/0.57    r1_ordinal1(sK1,sK0) | r1_ordinal1(sK0,sK1)),
% 1.45/0.57    inference(resolution,[],[f111,f27])).
% 1.45/0.57  fof(f111,plain,(
% 1.45/0.57    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(X0,sK1) | r1_ordinal1(sK1,X0)) )),
% 1.45/0.57    inference(resolution,[],[f32,f26])).
% 1.45/0.57  fof(f32,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f19])).
% 1.45/0.57  fof(f19,plain,(
% 1.45/0.57    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.45/0.57    inference(flattening,[],[f18])).
% 1.45/0.57  fof(f18,plain,(
% 1.45/0.57    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f5])).
% 1.45/0.57  fof(f5,axiom,(
% 1.45/0.57    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 1.45/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 1.45/0.57  fof(f207,plain,(
% 1.45/0.57    r2_hidden(sK0,sK1) | r1_tarski(sK0,sK1)),
% 1.45/0.57    inference(resolution,[],[f203,f133])).
% 1.45/0.57  fof(f133,plain,(
% 1.45/0.57    r2_hidden(sK1,sK0) | r1_tarski(sK0,sK1)),
% 1.45/0.57    inference(subsumption_resolution,[],[f132,f27])).
% 1.45/0.57  fof(f132,plain,(
% 1.45/0.57    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0)),
% 1.45/0.57    inference(subsumption_resolution,[],[f131,f26])).
% 1.45/0.57  fof(f131,plain,(
% 1.45/0.57    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0)),
% 1.45/0.57    inference(resolution,[],[f128,f31])).
% 1.45/0.57  fof(f203,plain,(
% 1.45/0.57    ~r2_hidden(sK1,sK0) | r2_hidden(sK0,sK1)),
% 1.45/0.57    inference(resolution,[],[f192,f75])).
% 1.45/0.57  fof(f75,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X0) | ~r2_hidden(X0,X1)) )),
% 1.45/0.57    inference(resolution,[],[f62,f45])).
% 1.45/0.57  fof(f62,plain,(
% 1.45/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 1.45/0.57    inference(equality_resolution,[],[f50])).
% 1.45/0.57  fof(f50,plain,(
% 1.45/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f2])).
% 1.45/0.57  fof(f192,plain,(
% 1.45/0.57    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | r2_hidden(sK0,sK1)),
% 1.45/0.57    inference(resolution,[],[f185,f53])).
% 1.45/0.57  fof(f53,plain,(
% 1.45/0.57    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | r2_hidden(sK0,sK1)),
% 1.45/0.57    inference(definition_unfolding,[],[f24,f29])).
% 1.45/0.57  fof(f24,plain,(
% 1.45/0.57    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f14])).
% 1.45/0.57  fof(f185,plain,(
% 1.45/0.57    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 1.45/0.57    inference(resolution,[],[f129,f27])).
% 1.45/0.57  fof(f129,plain,(
% 1.45/0.57    ( ! [X0] : (~v3_ordinal1(X0) | ~r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK1) | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),sK1)) )),
% 1.45/0.57    inference(resolution,[],[f124,f55])).
% 1.45/0.57  fof(f280,plain,(
% 1.45/0.57    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 1.45/0.57    inference(subsumption_resolution,[],[f250,f266])).
% 1.45/0.57  fof(f266,plain,(
% 1.45/0.57    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK0)),
% 1.45/0.57    inference(forward_demodulation,[],[f265,f215])).
% 1.45/0.57  fof(f265,plain,(
% 1.45/0.57    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 1.45/0.57    inference(subsumption_resolution,[],[f220,f163])).
% 1.45/0.57  fof(f220,plain,(
% 1.45/0.57    r2_hidden(sK0,sK0) | r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 1.45/0.57    inference(backward_demodulation,[],[f53,f215])).
% 1.45/0.57  fof(f250,plain,(
% 1.45/0.57    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK0) | r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 1.45/0.57    inference(backward_demodulation,[],[f185,f215])).
% 1.45/0.57  % SZS output end Proof for theBenchmark
% 1.45/0.57  % (6917)------------------------------
% 1.45/0.57  % (6917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (6917)Termination reason: Refutation
% 1.45/0.57  
% 1.45/0.57  % (6917)Memory used [KB]: 6396
% 1.45/0.57  % (6917)Time elapsed: 0.115 s
% 1.45/0.57  % (6917)------------------------------
% 1.45/0.57  % (6917)------------------------------
% 1.45/0.57  % (6910)Success in time 0.201 s
%------------------------------------------------------------------------------
