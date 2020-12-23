%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 158 expanded)
%              Number of leaves         :   18 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  213 ( 505 expanded)
%              Number of equality atoms :   34 ( 152 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f53,f64,f67,f72,f88,f91,f106,f115,f136])).

fof(f136,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f134,f23])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
      | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
          | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
        | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
            & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
            & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).

fof(f134,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f132,f24])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f132,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f71,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f71,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_6
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f115,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f111,f23])).

fof(f111,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_11 ),
    inference(resolution,[],[f105,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k7_relat_1(X1,X0),k7_relat_1(k7_relat_1(X1,X0),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f29,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).

fof(f105,plain,
    ( ~ sQ3_eqProxy(k7_relat_1(sK2,sK1),k7_relat_1(k7_relat_1(sK2,sK1),sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_11
  <=> sQ3_eqProxy(k7_relat_1(sK2,sK1),k7_relat_1(k7_relat_1(sK2,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f106,plain,
    ( ~ spl4_11
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f100,f86,f103])).

fof(f86,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ sQ3_eqProxy(k7_relat_1(sK2,X0),k7_relat_1(k7_relat_1(sK2,sK1),X0))
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f100,plain,
    ( ~ sQ3_eqProxy(k7_relat_1(sK2,sK1),k7_relat_1(k7_relat_1(sK2,sK1),sK1))
    | ~ spl4_9 ),
    inference(resolution,[],[f87,f24])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ sQ3_eqProxy(k7_relat_1(sK2,X0),k7_relat_1(k7_relat_1(sK2,sK1),X0)) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f91,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f89,f23])).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_8 ),
    inference(resolution,[],[f84,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f84,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_8
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f88,plain,
    ( ~ spl4_8
    | spl4_9
    | spl4_2 ),
    inference(avatar_split_clause,[],[f80,f44,f86,f82])).

fof(f44,plain,
    ( spl4_2
  <=> sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ sQ3_eqProxy(k7_relat_1(sK2,X0),k7_relat_1(k7_relat_1(sK2,sK1),X0))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(k7_relat_1(sK2,sK1)) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f79,f23])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ sQ3_eqProxy(k7_relat_1(sK2,X0),k7_relat_1(k7_relat_1(sK2,sK1),X0))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(k7_relat_1(sK2,sK1))
        | ~ v1_relat_1(sK2) )
    | spl4_2 ),
    inference(resolution,[],[f34,f46])).

fof(f46,plain,
    ( ~ sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK1),sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ3_eqProxy(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
      | ~ sQ3_eqProxy(k7_relat_1(X0,X3),k7_relat_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f26,f32,f32])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | k7_relat_1(X0,X3) != k7_relat_1(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              | k7_relat_1(X0,X3) != k7_relat_1(X1,X3)
              | ~ r1_tarski(X2,X3) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              | k7_relat_1(X0,X3) != k7_relat_1(X1,X3)
              | ~ r1_tarski(X2,X3) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t188_relat_1)).

fof(f72,plain,
    ( spl4_6
    | spl4_5 ),
    inference(avatar_split_clause,[],[f68,f61,f70])).

fof(f61,plain,
    ( spl4_5
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X0) )
    | spl4_5 ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f63,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f67,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f65,f23])).

fof(f65,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_4 ),
    inference(resolution,[],[f59,f27])).

fof(f59,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_4
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f64,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | spl4_3 ),
    inference(avatar_split_clause,[],[f55,f50,f61,f57])).

fof(f50,plain,
    ( spl4_3
  <=> sQ3_eqProxy(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f55,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl4_3 ),
    inference(resolution,[],[f36,f52])).

fof(f52,plain,
    ( ~ sQ3_eqProxy(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k7_relat_1(X1,X0),X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f30,f32])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f53,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f48,f40,f50])).

fof(f40,plain,
    ( spl4_1
  <=> sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f48,plain,
    ( ~ sQ3_eqProxy(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0))
    | spl4_1 ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f32])).

fof(f42,plain,
    ( ~ sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK0),sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f47,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f33,f44,f40])).

fof(f33,plain,
    ( ~ sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK1),sK0))
    | ~ sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(equality_proxy_replacement,[],[f25,f32,f32])).

fof(f25,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (13059)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.48  % (13067)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.48  % (13051)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.48  % (13049)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (13058)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.49  % (13054)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.49  % (13055)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.50  % (13068)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (13066)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.50  % (13050)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.51  % (13065)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (13060)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (13069)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.51  % (13063)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (13069)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f47,f53,f64,f67,f72,f88,f91,f106,f115,f136])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    ~spl4_6),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    $false | ~spl4_6),
% 0.20/0.51    inference(subsumption_resolution,[],[f134,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    v1_relat_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    (k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => ((k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.51  fof(f8,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f7])).
% 0.20/0.51  fof(f7,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | ~spl4_6),
% 0.20/0.51    inference(subsumption_resolution,[],[f132,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK2) | ~spl4_6),
% 0.20/0.51    inference(resolution,[],[f71,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X0) | ~r1_tarski(X0,sK1)) ) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl4_6 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    spl4_11),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    $false | spl4_11),
% 0.20/0.51    inference(subsumption_resolution,[],[f111,f23])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | spl4_11),
% 0.20/0.51    inference(resolution,[],[f105,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sQ3_eqProxy(k7_relat_1(X1,X0),k7_relat_1(k7_relat_1(X1,X0),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f29,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.51    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ~sQ3_eqProxy(k7_relat_1(sK2,sK1),k7_relat_1(k7_relat_1(sK2,sK1),sK1)) | spl4_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f103])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    spl4_11 <=> sQ3_eqProxy(k7_relat_1(sK2,sK1),k7_relat_1(k7_relat_1(sK2,sK1),sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ~spl4_11 | ~spl4_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f100,f86,f103])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl4_9 <=> ! [X0] : (~sQ3_eqProxy(k7_relat_1(sK2,X0),k7_relat_1(k7_relat_1(sK2,sK1),X0)) | ~r1_tarski(sK0,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ~sQ3_eqProxy(k7_relat_1(sK2,sK1),k7_relat_1(k7_relat_1(sK2,sK1),sK1)) | ~spl4_9),
% 0.20/0.51    inference(resolution,[],[f87,f24])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(sK0,X0) | ~sQ3_eqProxy(k7_relat_1(sK2,X0),k7_relat_1(k7_relat_1(sK2,sK1),X0))) ) | ~spl4_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl4_8),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    $false | spl4_8),
% 0.20/0.51    inference(subsumption_resolution,[],[f89,f23])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | spl4_8),
% 0.20/0.51    inference(resolution,[],[f84,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl4_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl4_8 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ~spl4_8 | spl4_9 | spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f80,f44,f86,f82])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    spl4_2 <=> sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK1),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X0] : (~sQ3_eqProxy(k7_relat_1(sK2,X0),k7_relat_1(k7_relat_1(sK2,sK1),X0)) | ~r1_tarski(sK0,X0) | ~v1_relat_1(k7_relat_1(sK2,sK1))) ) | spl4_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f79,f23])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0] : (~sQ3_eqProxy(k7_relat_1(sK2,X0),k7_relat_1(k7_relat_1(sK2,sK1),X0)) | ~r1_tarski(sK0,X0) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2)) ) | spl4_2),
% 0.20/0.51    inference(resolution,[],[f34,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ~sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK1),sK0)) | spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f44])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (sQ3_eqProxy(k7_relat_1(X0,X2),k7_relat_1(X1,X2)) | ~sQ3_eqProxy(k7_relat_1(X0,X3),k7_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f26,f32,f32])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | k7_relat_1(X0,X3) != k7_relat_1(X1,X3) | ~r1_tarski(X2,X3) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2,X3] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | k7_relat_1(X0,X3) != k7_relat_1(X1,X3) | ~r1_tarski(X2,X3)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2,X3] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k7_relat_1(X0,X3) != k7_relat_1(X1,X3) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2,X3] : ((k7_relat_1(X0,X3) = k7_relat_1(X1,X3) & r1_tarski(X2,X3)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t188_relat_1)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl4_6 | spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f68,f61,f70])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    spl4_5 <=> r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),X0)) ) | spl4_5),
% 0.20/0.51    inference(resolution,[],[f63,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f61])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    spl4_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    $false | spl4_4),
% 0.20/0.51    inference(subsumption_resolution,[],[f65,f23])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | spl4_4),
% 0.20/0.51    inference(resolution,[],[f59,f27])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    spl4_4 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ~spl4_4 | ~spl4_5 | spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f55,f50,f61,f57])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl4_3 <=> sQ3_eqProxy(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl4_3),
% 0.20/0.51    inference(resolution,[],[f36,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ~sQ3_eqProxy(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0)) | spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f50])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sQ3_eqProxy(k7_relat_1(X1,X0),X1) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f30,f32])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ~spl4_3 | spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f48,f40,f50])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    spl4_1 <=> sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ~sQ3_eqProxy(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0)) | spl4_1),
% 0.20/0.51    inference(resolution,[],[f42,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.20/0.51    inference(equality_proxy_axiom,[],[f32])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ~sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK0),sK1)) | spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f40])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ~spl4_1 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f33,f44,f40])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ~sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK1),sK0)) | ~sQ3_eqProxy(k7_relat_1(sK2,sK0),k7_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f25,f32,f32])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (13069)------------------------------
% 0.20/0.51  % (13069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13069)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (13069)Memory used [KB]: 10618
% 0.20/0.51  % (13069)Time elapsed: 0.095 s
% 0.20/0.51  % (13069)------------------------------
% 0.20/0.51  % (13069)------------------------------
% 0.20/0.51  % (13057)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (13052)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (13047)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (13048)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (13064)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.51  % (13053)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (13056)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  % (13045)Success in time 0.16 s
%------------------------------------------------------------------------------
