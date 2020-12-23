%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0672+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:44 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   27 (  56 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 231 expanded)
%              Number of equality atoms :   25 (  84 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1542,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1541,f1069])).

fof(f1069,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f1040])).

fof(f1040,plain,
    ( ( k8_relat_1(sK2,sK4) != k8_relat_1(sK2,k8_relat_1(sK3,sK4))
      | k8_relat_1(sK2,sK4) != k8_relat_1(sK3,k8_relat_1(sK2,sK4)) )
    & r1_tarski(sK2,sK3)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f982,f1039])).

fof(f1039,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
          | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
        & r1_tarski(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k8_relat_1(sK2,sK4) != k8_relat_1(sK2,k8_relat_1(sK3,sK4))
        | k8_relat_1(sK2,sK4) != k8_relat_1(sK3,k8_relat_1(sK2,sK4)) )
      & r1_tarski(sK2,sK3)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f982,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f981])).

fof(f981,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f978])).

fof(f978,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f977])).

fof(f977,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
          & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

fof(f1541,plain,(
    ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f1534,f1071])).

fof(f1071,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f1040])).

fof(f1534,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f1345,f1167])).

fof(f1167,plain,(
    ! [X2,X0,X1] :
      ( sQ14_eqProxy(k8_relat_1(X0,X2),k8_relat_1(X0,k8_relat_1(X1,X2)))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_proxy_replacement,[],[f1081,f1164])).

fof(f1164,plain,(
    ! [X1,X0] :
      ( sQ14_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ14_eqProxy])])).

fof(f1081,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f991])).

fof(f991,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f990])).

fof(f990,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f733])).

fof(f733,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

fof(f1345,plain,(
    ~ sQ14_eqProxy(k8_relat_1(sK2,sK4),k8_relat_1(sK2,k8_relat_1(sK3,sK4))) ),
    inference(subsumption_resolution,[],[f1344,f1069])).

fof(f1344,plain,
    ( ~ sQ14_eqProxy(k8_relat_1(sK2,sK4),k8_relat_1(sK2,k8_relat_1(sK3,sK4)))
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f1337,f1071])).

fof(f1337,plain,
    ( ~ sQ14_eqProxy(k8_relat_1(sK2,sK4),k8_relat_1(sK2,k8_relat_1(sK3,sK4)))
    | ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f1165,f1168])).

fof(f1168,plain,(
    ! [X2,X0,X1] :
      ( sQ14_eqProxy(k8_relat_1(X0,X2),k8_relat_1(X1,k8_relat_1(X0,X2)))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_proxy_replacement,[],[f1082,f1164])).

% (4009)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
fof(f1082,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f993])).

fof(f993,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f992])).

fof(f992,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f732])).

fof(f732,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f1165,plain,
    ( ~ sQ14_eqProxy(k8_relat_1(sK2,sK4),k8_relat_1(sK3,k8_relat_1(sK2,sK4)))
    | ~ sQ14_eqProxy(k8_relat_1(sK2,sK4),k8_relat_1(sK2,k8_relat_1(sK3,sK4))) ),
    inference(equality_proxy_replacement,[],[f1072,f1164,f1164])).

fof(f1072,plain,
    ( k8_relat_1(sK2,sK4) != k8_relat_1(sK2,k8_relat_1(sK3,sK4))
    | k8_relat_1(sK2,sK4) != k8_relat_1(sK3,k8_relat_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f1040])).
%------------------------------------------------------------------------------
