%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1086+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  28 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  82 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19,f10])).

fof(f10,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ v1_finset_1(k2_xboole_0(sK0,sK1))
    & v1_finset_1(sK1)
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k2_xboole_0(X0,X1))
        & v1_finset_1(X1)
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k2_xboole_0(sK0,sK1))
      & v1_finset_1(sK1)
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k2_xboole_0(X0,X1))
      & v1_finset_1(X1)
      & v1_finset_1(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k2_xboole_0(X0,X1))
      & v1_finset_1(X1)
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_finset_1(X1)
          & v1_finset_1(X0) )
       => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_finset_1)).

fof(f19,plain,(
    ~ v1_finset_1(sK0) ),
    inference(subsumption_resolution,[],[f18,f11])).

fof(f11,plain,(
    v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,
    ( ~ v1_finset_1(sK1)
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f12,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_finset_1)).

fof(f12,plain,(
    ~ v1_finset_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
