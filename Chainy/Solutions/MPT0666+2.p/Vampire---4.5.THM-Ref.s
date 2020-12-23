%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0666+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:43 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.89s
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
fof(f2089,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2088,f1063])).

fof(f1063,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1044])).

fof(f1044,plain,
    ( ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
      | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
    & r1_tarski(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f974,f1043])).

fof(f1043,plain,
    ( ? [X0,X1,X2] :
        ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
          | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
        & r1_tarski(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
        | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
      & r1_tarski(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f974,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f973])).

fof(f973,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f970])).

fof(f970,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
            & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f969])).

fof(f969,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).

fof(f2088,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f2085,f1065])).

fof(f1065,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f1044])).

fof(f2085,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1353,f1157])).

fof(f1157,plain,(
    ! [X2,X0,X1] :
      ( sQ10_eqProxy(k7_relat_1(X2,X0),k7_relat_1(k7_relat_1(X2,X0),X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_proxy_replacement,[],[f1071,f1155])).

fof(f1155,plain,(
    ! [X1,X0] :
      ( sQ10_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).

fof(f1071,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f979])).

fof(f979,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f978])).

fof(f978,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f707])).

fof(f707,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(f1353,plain,(
    ~ sQ10_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(subsumption_resolution,[],[f1352,f1063])).

fof(f1352,plain,
    ( ~ sQ10_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK0),sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1348,f1065])).

fof(f1348,plain,
    ( ~ sQ10_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK0),sK1))
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1156,f1158])).

fof(f1158,plain,(
    ! [X2,X0,X1] :
      ( sQ10_eqProxy(k7_relat_1(X2,X0),k7_relat_1(k7_relat_1(X2,X1),X0))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_proxy_replacement,[],[f1072,f1155])).

fof(f1072,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f981])).

fof(f981,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f980])).

fof(f980,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f708])).

fof(f708,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f1156,plain,
    ( ~ sQ10_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK1),sK0))
    | ~ sQ10_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(equality_proxy_replacement,[],[f1066,f1155,f1155])).

fof(f1066,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f1044])).
%------------------------------------------------------------------------------
