%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0672+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:25 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   47 (  77 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :  142 ( 259 expanded)
%              Number of equality atoms :   39 (  76 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f42,f46,f50,f55,f59,f64,f67])).

fof(f67,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f26,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_2
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X1,sK2)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f64,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f60,f48,f39,f62])).

fof(f39,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f48,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X0,k8_relat_1(X1,sK2)) )
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f49,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f59,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f56,f53,f29,f20])).

fof(f20,plain,
    ( spl3_1
  <=> k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f53,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f56,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f54,f31])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f55,plain,
    ( spl3_8
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f51,f44,f39,f53])).

fof(f44,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,sK2) = k8_relat_1(X1,k8_relat_1(X0,sK2)) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(resolution,[],[f45,f41])).

fof(f45,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f50,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f18,f48])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

fof(f46,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(f42,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f13,f39])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
      | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
    & r1_tarski(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
          | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
        & r1_tarski(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
        | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
      & r1_tarski(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
          & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_funct_1)).

fof(f32,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f16,f24,f20])).

fof(f16,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
