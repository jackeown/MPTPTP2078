%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 311 expanded)
%              Number of leaves         :    4 (  77 expanded)
%              Depth                    :   23
%              Number of atoms          :  112 ( 863 expanded)
%              Number of equality atoms :   10 ( 124 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f58])).

fof(f58,plain,(
    ~ r2_hidden(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f55,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f55,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f53,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f53,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f52,f26])).

fof(f26,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f8,f11])).

fof(f11,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f8,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <~> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
      <=> ~ ( r2_hidden(X0,X1)
          <=> r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f52,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f51,f41])).

fof(f41,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f40,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f39,f33])).

fof(f39,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | r2_hidden(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | r2_hidden(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,plain,
    ( r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK2) ),
    inference(definition_unfolding,[],[f9,f11])).

fof(f9,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f50,f31])).

fof(f50,plain,(
    ~ r2_hidden(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f48,f32])).

fof(f48,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f45,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f27,f41])).

fof(f27,plain,
    ( ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f7,f11])).

fof(f7,plain,
    ( ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f70,plain,(
    r2_hidden(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f69,f50])).

fof(f69,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | r2_hidden(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f63,f30])).

fof(f63,plain,(
    r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f62,f52])).

fof(f62,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(resolution,[],[f59,f24])).

fof(f24,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f10,f11])).

fof(f10,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f58,f40])).

%------------------------------------------------------------------------------
