%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1057+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:04 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   19 (  34 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 ( 120 expanded)
%              Number of equality atoms :   14 (  33 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2305,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2304,f1837])).

fof(f1837,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1781])).

fof(f1781,plain,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(sK2,sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1649,f1780,f1779])).

fof(f1779,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(X2,X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1780,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(X2,X1) )
   => ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1649,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1648])).

fof(f1648,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1584])).

fof(f1584,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X2,X1)
           => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f1583])).

fof(f1583,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X2,X1)
         => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_2)).

fof(f2304,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f2295,f1839])).

fof(f1839,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f1781])).

fof(f2295,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f1996,f2056])).

fof(f2056,plain,(
    ! [X2,X0,X1] :
      ( sQ22_eqProxy(k9_relat_1(X0,X1),k9_relat_1(k7_relat_1(X0,X2),X1))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1952,f1995])).

fof(f1995,plain,(
    ! [X1,X0] :
      ( sQ22_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ22_eqProxy])])).

fof(f1952,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1764])).

fof(f1764,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f766])).

fof(f766,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f1996,plain,(
    ~ sQ22_eqProxy(k9_relat_1(sK0,sK2),k9_relat_1(k7_relat_1(sK0,sK1),sK2)) ),
    inference(equality_proxy_replacement,[],[f1840,f1995])).

fof(f1840,plain,(
    k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f1781])).
%------------------------------------------------------------------------------
