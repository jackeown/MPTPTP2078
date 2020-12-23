%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0602+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    9 (  10 expanded)
%              Number of leaves         :    2 (   3 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  16 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8,f6])).

fof(f6,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(f8,plain,(
    ~ v4_relat_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f5,f7])).

fof(f7,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,plain,
    ( ~ v4_relat_1(k1_xboole_0,sK0)
    | ~ v5_relat_1(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ~ v5_relat_1(k1_xboole_0,X1)
      | ~ v4_relat_1(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v5_relat_1(k1_xboole_0,X1)
        & v4_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t206_relat_1)).

%------------------------------------------------------------------------------
