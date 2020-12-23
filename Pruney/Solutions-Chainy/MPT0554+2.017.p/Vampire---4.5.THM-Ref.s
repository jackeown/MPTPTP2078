%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 143 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :    7
%              Number of atoms          :  263 ( 414 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f53,f61,f65,f69,f73,f80,f95,f120,f146,f198,f227,f230])).

fof(f230,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_37 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f228,f39])).

fof(f39,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f228,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1
    | ~ spl3_37 ),
    inference(resolution,[],[f226,f34])).

fof(f34,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl3_37
  <=> ! [X1,X0] :
        ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f227,plain,
    ( spl3_37
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f223,f196,f71,f42,f225])).

fof(f42,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f71,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f196,plain,
    ( spl3_32
  <=> ! [X1,X0] :
        ( r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0))
        | ~ r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f222,f44])).

fof(f44,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_10
    | ~ spl3_32 ),
    inference(resolution,[],[f197,f72])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0))
        | r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0)) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f196])).

fof(f198,plain,
    ( spl3_32
    | ~ spl3_14
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f194,f144,f118,f93,f196])).

fof(f93,plain,
    ( spl3_14
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f118,plain,
    ( spl3_19
  <=> ! [X7] : k2_relat_1(k7_relat_1(sK2,X7)) = k9_relat_1(sK2,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f144,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1))
        | ~ r1_tarski(k7_relat_1(sK2,X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0))
        | ~ r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0)) )
    | ~ spl3_14
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f191,f94])).

fof(f94,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0))
        | ~ r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0))
        | ~ v1_relat_1(k7_relat_1(sK2,X0)) )
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(superposition,[],[f145,f119])).

fof(f119,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(sK2,X7)) = k9_relat_1(sK2,X7)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f118])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1))
        | ~ r1_tarski(k7_relat_1(sK2,X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,
    ( spl3_23
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f142,f118,f93,f51,f144])).

fof(f51,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1))
        | ~ r1_tarski(k7_relat_1(sK2,X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f138,f94])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1))
        | ~ r1_tarski(k7_relat_1(sK2,X0),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k7_relat_1(sK2,X0)) )
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(superposition,[],[f52,f119])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f120,plain,
    ( spl3_19
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f104,f63,f42,f118])).

fof(f63,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f104,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(sK2,X7)) = k9_relat_1(sK2,X7)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f64,f44])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f95,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f91,f78,f67,f47,f42,f93])).

fof(f47,plain,
    ( spl3_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f67,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f78,plain,
    ( spl3_11
  <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f91,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f90,f48])).

fof(f48,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f90,plain,
    ( ! [X0] :
        ( v1_relat_1(k7_relat_1(sK2,X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f89,f44])).

fof(f89,plain,
    ( ! [X0] :
        ( v1_relat_1(k7_relat_1(sK2,X0))
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(superposition,[],[f68,f79])).

fof(f79,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f80,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f74,f59,f42,f78])).

fof(f59,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f60,f44])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f73,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

fof(f69,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f65,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f61,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f53,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f49,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f32])).

fof(f23,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:02:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (6528)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (6530)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (6525)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.44  % (6529)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.46  % (6526)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.47  % (6533)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.47  % (6532)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.47  % (6533)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f231,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f53,f61,f65,f69,f73,f80,f95,f120,f146,f198,f227,f230])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    spl3_1 | ~spl3_2 | ~spl3_37),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    $false | (spl3_1 | ~spl3_2 | ~spl3_37)),
% 0.21/0.47    inference(subsumption_resolution,[],[f228,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK1) | (spl3_1 | ~spl3_37)),
% 0.21/0.47    inference(resolution,[],[f226,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl3_1 <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f226,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_37),
% 0.21/0.47    inference(avatar_component_clause,[],[f225])).
% 0.21/0.47  fof(f225,plain,(
% 0.21/0.47    spl3_37 <=> ! [X1,X0] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    spl3_37 | ~spl3_3 | ~spl3_10 | ~spl3_32),
% 0.21/0.47    inference(avatar_split_clause,[],[f223,f196,f71,f42,f225])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl3_3 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl3_10 <=> ! [X1,X0,X2] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    spl3_32 <=> ! [X1,X0] : (r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0)) | ~r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,X1)) ) | (~spl3_3 | ~spl3_10 | ~spl3_32)),
% 0.21/0.47    inference(subsumption_resolution,[],[f222,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f42])).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(sK2)) ) | (~spl3_10 | ~spl3_32)),
% 0.21/0.47    inference(resolution,[],[f197,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) ) | ~spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f197,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0)) | r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0))) ) | ~spl3_32),
% 0.21/0.47    inference(avatar_component_clause,[],[f196])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    spl3_32 | ~spl3_14 | ~spl3_19 | ~spl3_23),
% 0.21/0.47    inference(avatar_split_clause,[],[f194,f144,f118,f93,f196])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    spl3_14 <=> ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl3_19 <=> ! [X7] : k2_relat_1(k7_relat_1(sK2,X7)) = k9_relat_1(sK2,X7)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    spl3_23 <=> ! [X1,X0] : (r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) | ~r1_tarski(k7_relat_1(sK2,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0)) | ~r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0))) ) | (~spl3_14 | ~spl3_19 | ~spl3_23)),
% 0.21/0.47    inference(subsumption_resolution,[],[f191,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f93])).
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0)) | ~r1_tarski(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) ) | (~spl3_19 | ~spl3_23)),
% 0.21/0.47    inference(superposition,[],[f145,f119])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ( ! [X7] : (k2_relat_1(k7_relat_1(sK2,X7)) = k9_relat_1(sK2,X7)) ) | ~spl3_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f118])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) | ~r1_tarski(k7_relat_1(sK2,X0),X1) | ~v1_relat_1(X1)) ) | ~spl3_23),
% 0.21/0.47    inference(avatar_component_clause,[],[f144])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    spl3_23 | ~spl3_5 | ~spl3_14 | ~spl3_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f142,f118,f93,f51,f144])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl3_5 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) | ~r1_tarski(k7_relat_1(sK2,X0),X1) | ~v1_relat_1(X1)) ) | (~spl3_5 | ~spl3_14 | ~spl3_19)),
% 0.21/0.47    inference(subsumption_resolution,[],[f138,f94])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) | ~r1_tarski(k7_relat_1(sK2,X0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k7_relat_1(sK2,X0))) ) | (~spl3_5 | ~spl3_19)),
% 0.21/0.47    inference(superposition,[],[f52,f119])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f51])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    spl3_19 | ~spl3_3 | ~spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f104,f63,f42,f118])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl3_8 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X7] : (k2_relat_1(k7_relat_1(sK2,X7)) = k9_relat_1(sK2,X7)) ) | (~spl3_3 | ~spl3_8)),
% 0.21/0.47    inference(resolution,[],[f64,f44])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl3_14 | ~spl3_3 | ~spl3_4 | ~spl3_9 | ~spl3_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f91,f78,f67,f47,f42,f93])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl3_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl3_9 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl3_11 <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) ) | (~spl3_3 | ~spl3_4 | ~spl3_9 | ~spl3_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f90,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl3_3 | ~spl3_9 | ~spl3_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f89,f44])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0)) | ~v1_relat_1(sK2) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl3_9 | ~spl3_11)),
% 0.21/0.47    inference(superposition,[],[f68,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | ~spl3_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f78])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl3_11 | ~spl3_3 | ~spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f74,f59,f42,f78])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl3_7 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | (~spl3_3 | ~spl3_7)),
% 0.21/0.47    inference(resolution,[],[f60,f44])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f71])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f67])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f63])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f59])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f51])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f47])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f42])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f37])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f32])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (6533)------------------------------
% 0.21/0.48  % (6533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6533)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (6533)Memory used [KB]: 6140
% 0.21/0.48  % (6533)Time elapsed: 0.065 s
% 0.21/0.48  % (6533)------------------------------
% 0.21/0.48  % (6533)------------------------------
% 0.21/0.48  % (6522)Success in time 0.118 s
%------------------------------------------------------------------------------
