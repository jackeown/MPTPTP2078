%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0681+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:44 EST 2020

% Result     : Theorem 2.37s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 159 expanded)
%              Number of leaves         :    9 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  131 ( 590 expanded)
%              Number of equality atoms :   26 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3629,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3628,f3594])).

fof(f3594,plain,(
    ! [X37] : ~ r2_hidden(X37,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3593,f3592])).

fof(f3592,plain,(
    k1_xboole_0 = k4_xboole_0(sK28,sK28) ),
    inference(forward_demodulation,[],[f3586,f3573])).

fof(f3573,plain,(
    sK28 = k4_xboole_0(sK28,sK29) ),
    inference(resolution,[],[f1883,f2006])).

fof(f2006,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1585])).

fof(f1585,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f1883,plain,(
    r1_xboole_0(sK28,sK29) ),
    inference(cnf_transformation,[],[f1549])).

fof(f1549,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK30,sK28),k9_relat_1(sK30,sK29))
    & v2_funct_1(sK30)
    & r1_xboole_0(sK28,sK29)
    & v1_funct_1(sK30)
    & v1_relat_1(sK30) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29,sK30])],[f1001,f1548])).

fof(f1548,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK30,sK28),k9_relat_1(sK30,sK29))
      & v2_funct_1(sK30)
      & r1_xboole_0(sK28,sK29)
      & v1_funct_1(sK30)
      & v1_relat_1(sK30) ) ),
    introduced(choice_axiom,[])).

fof(f1001,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1000])).

fof(f1000,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f934])).

fof(f934,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f933])).

fof(f933,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

fof(f3586,plain,(
    k1_xboole_0 = k4_xboole_0(sK28,k4_xboole_0(sK28,sK29)) ),
    inference(resolution,[],[f1883,f2743])).

fof(f2743,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f2004,f2635])).

fof(f2635,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2004,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1584])).

fof(f1584,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f3593,plain,(
    ! [X37] : ~ r2_hidden(X37,k4_xboole_0(sK28,sK28)) ),
    inference(forward_demodulation,[],[f3587,f3573])).

fof(f3587,plain,(
    ! [X37] : ~ r2_hidden(X37,k4_xboole_0(sK28,k4_xboole_0(sK28,sK29))) ),
    inference(resolution,[],[f1883,f2748])).

fof(f2748,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f2018,f2635])).

fof(f2018,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1589])).

fof(f1589,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK46(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK46])],[f1100,f1588])).

fof(f1588,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK46(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f1100,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f994])).

fof(f994,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f3628,plain,(
    r2_hidden(sK46(k9_relat_1(sK30,sK28),k9_relat_1(sK30,sK29)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3627,f3047])).

fof(f3047,plain,(
    k1_xboole_0 = k9_relat_1(sK30,k1_xboole_0) ),
    inference(resolution,[],[f1881,f1932])).

fof(f1932,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1036])).

fof(f1036,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f751])).

fof(f751,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f1881,plain,(
    v1_relat_1(sK30) ),
    inference(cnf_transformation,[],[f1549])).

fof(f3627,plain,(
    r2_hidden(sK46(k9_relat_1(sK30,sK28),k9_relat_1(sK30,sK29)),k9_relat_1(sK30,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f3626,f3592])).

fof(f3626,plain,(
    r2_hidden(sK46(k9_relat_1(sK30,sK28),k9_relat_1(sK30,sK29)),k9_relat_1(sK30,k4_xboole_0(sK28,sK28))) ),
    inference(forward_demodulation,[],[f3625,f3573])).

fof(f3625,plain,(
    r2_hidden(sK46(k9_relat_1(sK30,sK28),k9_relat_1(sK30,sK29)),k9_relat_1(sK30,k4_xboole_0(sK28,k4_xboole_0(sK28,sK29)))) ),
    inference(forward_demodulation,[],[f3610,f3411])).

fof(f3411,plain,(
    ! [X401,X402] : k9_relat_1(sK30,k4_xboole_0(X401,k4_xboole_0(X401,X402))) = k4_xboole_0(k9_relat_1(sK30,X401),k4_xboole_0(k9_relat_1(sK30,X401),k9_relat_1(sK30,X402))) ),
    inference(subsumption_resolution,[],[f3410,f1882])).

fof(f1882,plain,(
    v1_funct_1(sK30) ),
    inference(cnf_transformation,[],[f1549])).

fof(f3410,plain,(
    ! [X401,X402] :
      ( k9_relat_1(sK30,k4_xboole_0(X401,k4_xboole_0(X401,X402))) = k4_xboole_0(k9_relat_1(sK30,X401),k4_xboole_0(k9_relat_1(sK30,X401),k9_relat_1(sK30,X402)))
      | ~ v1_funct_1(sK30) ) ),
    inference(subsumption_resolution,[],[f3292,f1884])).

fof(f1884,plain,(
    v2_funct_1(sK30) ),
    inference(cnf_transformation,[],[f1549])).

fof(f3292,plain,(
    ! [X401,X402] :
      ( k9_relat_1(sK30,k4_xboole_0(X401,k4_xboole_0(X401,X402))) = k4_xboole_0(k9_relat_1(sK30,X401),k4_xboole_0(k9_relat_1(sK30,X401),k9_relat_1(sK30,X402)))
      | ~ v2_funct_1(sK30)
      | ~ v1_funct_1(sK30) ) ),
    inference(resolution,[],[f1881,f2729])).

fof(f2729,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f1887,f2635,f2635])).

fof(f1887,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1005])).

fof(f1005,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1004])).

fof(f1004,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f929])).

fof(f929,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f3610,plain,(
    r2_hidden(sK46(k9_relat_1(sK30,sK28),k9_relat_1(sK30,sK29)),k4_xboole_0(k9_relat_1(sK30,sK28),k4_xboole_0(k9_relat_1(sK30,sK28),k9_relat_1(sK30,sK29)))) ),
    inference(resolution,[],[f1885,f2749])).

fof(f2749,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK46(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f2017,f2635])).

fof(f2017,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK46(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1589])).

fof(f1885,plain,(
    ~ r1_xboole_0(k9_relat_1(sK30,sK28),k9_relat_1(sK30,sK29)) ),
    inference(cnf_transformation,[],[f1549])).
%------------------------------------------------------------------------------
