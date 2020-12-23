%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0825+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 (  71 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1671,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1461,f1668])).

fof(f1668,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f1667])).

fof(f1667,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f1650,f1444])).

fof(f1444,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1347])).

fof(f1347,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1319])).

fof(f1319,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1318])).

fof(f1318,plain,(
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

fof(f1650,plain,
    ( ~ r1_tarski(k6_relat_1(sK0),k6_relat_1(sK0))
    | spl6_1 ),
    inference(resolution,[],[f1623,f1567])).

fof(f1567,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(sK0,sK0))
        | ~ r1_tarski(k6_relat_1(sK0),X0) )
    | spl6_1 ),
    inference(resolution,[],[f1341,f1460])).

fof(f1460,plain,
    ( ~ r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f1459])).

fof(f1459,plain,
    ( spl6_1
  <=> r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1341,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1241])).

fof(f1241,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1240])).

fof(f1240,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1623,plain,(
    ! [X5] : r1_tarski(k6_relat_1(X5),k2_zfmisc_1(X5,X5)) ),
    inference(forward_demodulation,[],[f1622,f1435])).

fof(f1435,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1622,plain,(
    ! [X5] : r1_tarski(k6_relat_1(X5),k2_zfmisc_1(k1_relat_1(k6_relat_1(X5)),X5)) ),
    inference(forward_demodulation,[],[f1621,f1436])).

fof(f1436,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f1621,plain,(
    ! [X5] : r1_tarski(k6_relat_1(X5),k2_zfmisc_1(k1_relat_1(k6_relat_1(X5)),k2_relat_1(k6_relat_1(X5)))) ),
    inference(resolution,[],[f1395,f1437])).

fof(f1437,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f921])).

fof(f921,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f1395,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f1277])).

fof(f1277,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f825])).

fof(f825,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f1461,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f1340,f1459])).

fof(f1340,plain,(
    ~ r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f1313])).

fof(f1313,plain,(
    ~ r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1239,f1312])).

fof(f1312,plain,
    ( ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(choice_axiom,[])).

fof(f1239,plain,(
    ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f1235])).

fof(f1235,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f1234])).

fof(f1234,conjecture,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relset_1)).
%------------------------------------------------------------------------------
