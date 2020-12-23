%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0712+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:45 EST 2020

% Result     : Theorem 9.83s
% Output     : Refutation 9.83s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 110 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  149 ( 298 expanded)
%              Number of equality atoms :   44 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12078,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12031,f6300])).

fof(f6300,plain,(
    k1_relat_1(sK30) = k4_xboole_0(k1_relat_1(sK30),k2_tarski(sK29,sK29)) ),
    inference(resolution,[],[f3841,f3039])).

fof(f3039,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f2793,f2385])).

fof(f2385,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f2793,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1956])).

fof(f1956,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f421])).

fof(f421,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f3841,plain,(
    ~ r2_hidden(sK29,k1_relat_1(sK30)) ),
    inference(subsumption_resolution,[],[f3840,f1961])).

fof(f1961,plain,(
    v1_relat_1(sK30) ),
    inference(cnf_transformation,[],[f1611])).

fof(f1611,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK30,k1_tarski(sK29))),k1_tarski(k1_funct_1(sK30,sK29)))
    & v1_funct_1(sK30)
    & v1_relat_1(sK30) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29,sK30])],[f1039,f1610])).

fof(f1610,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK30,k1_tarski(sK29))),k1_tarski(k1_funct_1(sK30,sK29)))
      & v1_funct_1(sK30)
      & v1_relat_1(sK30) ) ),
    introduced(choice_axiom,[])).

fof(f1039,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1038])).

fof(f1038,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f976])).

fof(f976,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f975])).

fof(f975,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

fof(f3840,plain,
    ( ~ r2_hidden(sK29,k1_relat_1(sK30))
    | ~ v1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f3839,f1962])).

fof(f1962,plain,(
    v1_funct_1(sK30) ),
    inference(cnf_transformation,[],[f1611])).

fof(f3839,plain,
    ( ~ r2_hidden(sK29,k1_relat_1(sK30))
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f3815,f3054])).

fof(f3054,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1965])).

fof(f1965,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1613])).

fof(f1613,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1612])).

fof(f1612,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3815,plain,
    ( ~ r1_tarski(k9_relat_1(sK30,k2_tarski(sK29,sK29)),k9_relat_1(sK30,k2_tarski(sK29,sK29)))
    | ~ r2_hidden(sK29,k1_relat_1(sK30))
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(duplicate_literal_removal,[],[f3777])).

fof(f3777,plain,
    ( ~ r1_tarski(k9_relat_1(sK30,k2_tarski(sK29,sK29)),k9_relat_1(sK30,k2_tarski(sK29,sK29)))
    | ~ r2_hidden(sK29,k1_relat_1(sK30))
    | ~ r2_hidden(sK29,k1_relat_1(sK30))
    | ~ v1_funct_1(sK30)
    | ~ v1_relat_1(sK30) ),
    inference(superposition,[],[f3497,f1971])).

fof(f1971,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1045])).

fof(f1045,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1044])).

fof(f1044,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f935])).

fof(f935,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(f3497,plain,(
    ~ r1_tarski(k9_relat_1(sK30,k2_tarski(sK29,sK29)),k2_tarski(k1_funct_1(sK30,sK29),k1_funct_1(sK30,sK29))) ),
    inference(backward_demodulation,[],[f2822,f3276])).

fof(f3276,plain,(
    ! [X237] : k9_relat_1(sK30,X237) = k2_relat_1(k7_relat_1(sK30,X237)) ),
    inference(resolution,[],[f1961,f2311])).

fof(f2311,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1228])).

fof(f1228,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f750])).

fof(f750,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f2822,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK30,k2_tarski(sK29,sK29))),k2_tarski(k1_funct_1(sK30,sK29),k1_funct_1(sK30,sK29))) ),
    inference(definition_unfolding,[],[f1963,f2385,f2385])).

fof(f1963,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK30,k1_tarski(sK29))),k1_tarski(k1_funct_1(sK30,sK29))) ),
    inference(cnf_transformation,[],[f1611])).

fof(f12031,plain,(
    k1_relat_1(sK30) != k4_xboole_0(k1_relat_1(sK30),k2_tarski(sK29,sK29)) ),
    inference(resolution,[],[f3824,f2608])).

fof(f2608,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f1900])).

fof(f1900,plain,(
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

fof(f3824,plain,(
    ~ r1_xboole_0(k1_relat_1(sK30),k2_tarski(sK29,sK29)) ),
    inference(subsumption_resolution,[],[f3823,f1961])).

fof(f3823,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK30),k2_tarski(sK29,sK29))
    | ~ v1_relat_1(sK30) ),
    inference(subsumption_resolution,[],[f3766,f3068])).

fof(f3068,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f2857])).

fof(f2857,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f2149,f2385])).

fof(f2149,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1698])).

fof(f1698,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f1697])).

fof(f1697,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f313])).

fof(f313,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f3766,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(k1_funct_1(sK30,sK29),k1_funct_1(sK30,sK29)))
    | ~ r1_xboole_0(k1_relat_1(sK30),k2_tarski(sK29,sK29))
    | ~ v1_relat_1(sK30) ),
    inference(superposition,[],[f3497,f2308])).

fof(f2308,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1815])).

fof(f1815,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1225])).

fof(f1225,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f754])).

fof(f754,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
%------------------------------------------------------------------------------
