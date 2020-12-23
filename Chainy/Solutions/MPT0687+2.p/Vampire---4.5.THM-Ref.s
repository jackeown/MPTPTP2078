%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0687+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:44 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   36 (  95 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :   17
%              Number of atoms          :   96 ( 325 expanded)
%              Number of equality atoms :   24 ( 100 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3777,plain,(
    $false ),
    inference(global_subsumption,[],[f3691,f3776])).

fof(f3776,plain,(
    r1_xboole_0(k2_relat_1(sK106),k1_tarski(sK105)) ),
    inference(subsumption_resolution,[],[f3758,f2259])).

fof(f2259,plain,(
    v1_relat_1(sK106) ),
    inference(cnf_transformation,[],[f1773])).

fof(f1773,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK106,k1_tarski(sK105))
      | ~ r2_hidden(sK105,k2_relat_1(sK106)) )
    & ( k1_xboole_0 != k10_relat_1(sK106,k1_tarski(sK105))
      | r2_hidden(sK105,k2_relat_1(sK106)) )
    & v1_relat_1(sK106) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK105,sK106])],[f1771,f1772])).

fof(f1772,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK106,k1_tarski(sK105))
        | ~ r2_hidden(sK105,k2_relat_1(sK106)) )
      & ( k1_xboole_0 != k10_relat_1(sK106,k1_tarski(sK105))
        | r2_hidden(sK105,k2_relat_1(sK106)) )
      & v1_relat_1(sK106) ) ),
    introduced(choice_axiom,[])).

fof(f1771,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1770])).

fof(f1770,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1008])).

fof(f1008,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f943])).

fof(f943,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f942])).

fof(f942,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f3758,plain,
    ( r1_xboole_0(k2_relat_1(sK106),k1_tarski(sK105))
    | ~ v1_relat_1(sK106) ),
    inference(trivial_inequality_removal,[],[f3743])).

fof(f3743,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK106),k1_tarski(sK105))
    | ~ v1_relat_1(sK106) ),
    inference(superposition,[],[f2280,f3714])).

fof(f3714,plain,(
    k1_xboole_0 = k10_relat_1(sK106,k1_tarski(sK105)) ),
    inference(subsumption_resolution,[],[f2261,f3689])).

fof(f3689,plain,(
    r2_hidden(sK105,k2_relat_1(sK106)) ),
    inference(resolution,[],[f3687,f2844])).

fof(f2844,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1324])).

fof(f1324,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f306])).

fof(f306,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f3687,plain,(
    ~ r1_xboole_0(k1_tarski(sK105),k2_relat_1(sK106)) ),
    inference(subsumption_resolution,[],[f3680,f2834])).

fof(f2834,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1318])).

fof(f1318,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f305])).

fof(f305,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f3680,plain,
    ( r2_hidden(sK105,k2_relat_1(sK106))
    | ~ r1_xboole_0(k1_tarski(sK105),k2_relat_1(sK106)) ),
    inference(resolution,[],[f3679,f2842])).

fof(f2842,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1322])).

fof(f1322,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f3679,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK106),k1_tarski(sK105))
    | r2_hidden(sK105,k2_relat_1(sK106)) ),
    inference(subsumption_resolution,[],[f3678,f2259])).

fof(f3678,plain,
    ( r2_hidden(sK105,k2_relat_1(sK106))
    | ~ r1_xboole_0(k2_relat_1(sK106),k1_tarski(sK105))
    | ~ v1_relat_1(sK106) ),
    inference(trivial_inequality_removal,[],[f3677])).

fof(f3677,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK105,k2_relat_1(sK106))
    | ~ r1_xboole_0(k2_relat_1(sK106),k1_tarski(sK105))
    | ~ v1_relat_1(sK106) ),
    inference(superposition,[],[f2260,f2281])).

fof(f2281,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1780])).

fof(f1780,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1027])).

fof(f1027,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f775])).

fof(f775,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f2260,plain,
    ( k1_xboole_0 != k10_relat_1(sK106,k1_tarski(sK105))
    | r2_hidden(sK105,k2_relat_1(sK106)) ),
    inference(cnf_transformation,[],[f1773])).

fof(f2261,plain,
    ( k1_xboole_0 = k10_relat_1(sK106,k1_tarski(sK105))
    | ~ r2_hidden(sK105,k2_relat_1(sK106)) ),
    inference(cnf_transformation,[],[f1773])).

fof(f2280,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1780])).

fof(f3691,plain,(
    ~ r1_xboole_0(k2_relat_1(sK106),k1_tarski(sK105)) ),
    inference(resolution,[],[f3687,f2842])).
%------------------------------------------------------------------------------
