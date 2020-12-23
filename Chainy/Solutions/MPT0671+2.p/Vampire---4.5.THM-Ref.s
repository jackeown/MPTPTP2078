%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0671+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:43 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   32 (  54 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 149 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5171,f5180,f5185])).

fof(f5185,plain,(
    spl216_6 ),
    inference(avatar_contradiction_clause,[],[f5184])).

fof(f5184,plain,
    ( $false
    | spl216_6 ),
    inference(subsumption_resolution,[],[f5183,f2451])).

fof(f2451,plain,(
    v1_relat_1(sK18) ),
    inference(cnf_transformation,[],[f1888])).

fof(f1888,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK17,sK18)),k1_relat_1(sK18))
    & v1_funct_1(sK18)
    & v1_relat_1(sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f997,f1887])).

fof(f1887,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK17,sK18)),k1_relat_1(sK18))
      & v1_funct_1(sK18)
      & v1_relat_1(sK18) ) ),
    introduced(choice_axiom,[])).

fof(f997,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f996])).

fof(f996,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f976])).

fof(f976,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f975])).

fof(f975,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_funct_1)).

fof(f5183,plain,
    ( ~ v1_relat_1(sK18)
    | spl216_6 ),
    inference(resolution,[],[f5170,f2936])).

fof(f2936,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1224])).

fof(f1224,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f720])).

fof(f720,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f5170,plain,
    ( ~ r1_tarski(k8_relat_1(sK17,sK18),sK18)
    | spl216_6 ),
    inference(avatar_component_clause,[],[f5168])).

fof(f5168,plain,
    ( spl216_6
  <=> r1_tarski(k8_relat_1(sK17,sK18),sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl216_6])])).

fof(f5180,plain,(
    spl216_5 ),
    inference(avatar_contradiction_clause,[],[f5179])).

fof(f5179,plain,
    ( $false
    | spl216_5 ),
    inference(subsumption_resolution,[],[f5174,f2451])).

fof(f5174,plain,
    ( ~ v1_relat_1(sK18)
    | spl216_5 ),
    inference(resolution,[],[f5166,f2932])).

fof(f2932,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1220])).

fof(f1220,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f670])).

fof(f670,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f5166,plain,
    ( ~ v1_relat_1(k8_relat_1(sK17,sK18))
    | spl216_5 ),
    inference(avatar_component_clause,[],[f5164])).

fof(f5164,plain,
    ( spl216_5
  <=> v1_relat_1(k8_relat_1(sK17,sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl216_5])])).

fof(f5171,plain,
    ( ~ spl216_5
    | ~ spl216_6 ),
    inference(avatar_split_clause,[],[f5162,f5168,f5164])).

fof(f5162,plain,
    ( ~ r1_tarski(k8_relat_1(sK17,sK18),sK18)
    | ~ v1_relat_1(k8_relat_1(sK17,sK18)) ),
    inference(subsumption_resolution,[],[f5160,f2451])).

fof(f5160,plain,
    ( ~ r1_tarski(k8_relat_1(sK17,sK18),sK18)
    | ~ v1_relat_1(sK18)
    | ~ v1_relat_1(k8_relat_1(sK17,sK18)) ),
    inference(resolution,[],[f2453,f2610])).

fof(f2610,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1071])).

fof(f1071,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1070])).

fof(f1070,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f829])).

fof(f829,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f2453,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1(sK17,sK18)),k1_relat_1(sK18)) ),
    inference(cnf_transformation,[],[f1888])).
%------------------------------------------------------------------------------
