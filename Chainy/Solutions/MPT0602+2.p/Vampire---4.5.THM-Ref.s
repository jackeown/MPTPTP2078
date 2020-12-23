%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0602+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   11 (  12 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f906,plain,(
    $false ),
    inference(subsumption_resolution,[],[f905,f892])).

fof(f892,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(f905,plain,(
    ~ v4_relat_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f885,f893])).

fof(f893,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f696])).

fof(f885,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK1)
    | ~ v4_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f879])).

fof(f879,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK1)
    | ~ v4_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f871,f878])).

fof(f878,plain,
    ( ? [X0,X1] :
        ( ~ v5_relat_1(k1_xboole_0,X1)
        | ~ v4_relat_1(k1_xboole_0,X0) )
   => ( ~ v5_relat_1(k1_xboole_0,sK1)
      | ~ v4_relat_1(k1_xboole_0,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f871,plain,(
    ? [X0,X1] :
      ( ~ v5_relat_1(k1_xboole_0,X1)
      | ~ v4_relat_1(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f805])).

fof(f805,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v5_relat_1(k1_xboole_0,X1)
        & v4_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f804])).

fof(f804,conjecture,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t206_relat_1)).
%------------------------------------------------------------------------------
