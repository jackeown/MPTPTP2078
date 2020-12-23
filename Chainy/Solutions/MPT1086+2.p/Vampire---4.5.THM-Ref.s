%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1086+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  27 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  80 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2264,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2253,f1972])).

fof(f1972,plain,(
    ~ v1_finset_1(k2_xboole_0(sK14,sK15)) ),
    inference(cnf_transformation,[],[f1867])).

fof(f1867,plain,
    ( ~ v1_finset_1(k2_xboole_0(sK14,sK15))
    & v1_finset_1(sK15)
    & v1_finset_1(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f1717,f1866])).

fof(f1866,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k2_xboole_0(X0,X1))
        & v1_finset_1(X1)
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k2_xboole_0(sK14,sK15))
      & v1_finset_1(sK15)
      & v1_finset_1(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f1717,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k2_xboole_0(X0,X1))
      & v1_finset_1(X1)
      & v1_finset_1(X0) ) ),
    inference(flattening,[],[f1716])).

fof(f1716,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k2_xboole_0(X0,X1))
      & v1_finset_1(X1)
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1714])).

fof(f1714,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_finset_1(X1)
          & v1_finset_1(X0) )
       => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1713])).

fof(f1713,conjecture,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_finset_1)).

fof(f2253,plain,(
    v1_finset_1(k2_xboole_0(sK14,sK15)) ),
    inference(unit_resulting_resolution,[],[f1970,f1971,f2027])).

fof(f2027,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f1746])).

fof(f1746,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f1745])).

fof(f1745,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1710])).

fof(f1710,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_finset_1)).

fof(f1971,plain,(
    v1_finset_1(sK15) ),
    inference(cnf_transformation,[],[f1867])).

fof(f1970,plain,(
    v1_finset_1(sK14) ),
    inference(cnf_transformation,[],[f1867])).
%------------------------------------------------------------------------------
