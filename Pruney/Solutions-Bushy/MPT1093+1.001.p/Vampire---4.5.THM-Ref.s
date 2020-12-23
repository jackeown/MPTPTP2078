%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1093+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:15 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   53 (  93 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  181 ( 362 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f34,f39,f44,f48,f52,f60,f66])).

fof(f66,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f64,f43])).

fof(f43,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f64,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f63,f38])).

fof(f38,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f63,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f62,f28])).

fof(f28,plain,
    ( v1_finset_1(k10_relat_1(sK1,sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_2
  <=> v1_finset_1(k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f62,plain,
    ( ~ v1_finset_1(k10_relat_1(sK1,sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_1
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f61,f23])).

fof(f23,plain,
    ( ~ v1_finset_1(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl2_1
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f61,plain,
    ( v1_finset_1(sK0)
    | ~ v1_finset_1(k10_relat_1(sK1,sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(superposition,[],[f47,f59])).

fof(f59,plain,
    ( sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_8
  <=> sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( v1_finset_1(k9_relat_1(X0,X1))
        | ~ v1_finset_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( v1_finset_1(k9_relat_1(X0,X1))
        | ~ v1_finset_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f60,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f55,f50,f41,f36,f31,f57])).

fof(f31,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f50,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f55,plain,
    ( sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f54,f43])).

fof(f54,plain,
    ( sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f53,f38])).

fof(f53,plain,
    ( sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k2_relat_1(X1))
        | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f52,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f19,f50])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f48,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

fof(f44,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f13,f41])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ v1_finset_1(sK0)
    & v1_finset_1(k10_relat_1(sK1,sK0))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(X0)
        & v1_finset_1(k10_relat_1(X1,X0))
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v1_finset_1(sK0)
      & v1_finset_1(k10_relat_1(sK1,sK0))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v1_finset_1(k10_relat_1(X1,X0))
            & r1_tarski(X0,k2_relat_1(X1)) )
         => v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v1_finset_1(k10_relat_1(X1,X0))
          & r1_tarski(X0,k2_relat_1(X1)) )
       => v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_finset_1)).

fof(f39,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f14,f36])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f26])).

fof(f16,plain,(
    v1_finset_1(k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f21])).

fof(f17,plain,(
    ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
