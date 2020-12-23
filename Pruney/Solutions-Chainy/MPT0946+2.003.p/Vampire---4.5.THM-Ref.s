%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 335 expanded)
%              Number of leaves         :   19 (  96 expanded)
%              Depth                    :   16
%              Number of atoms          :  424 (1361 expanded)
%              Number of equality atoms :   59 ( 256 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f129,f146,f163,f165,f173])).

fof(f173,plain,
    ( spl4_2
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f171,f42])).

fof(f42,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK0 != sK1
    & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK0 != sK1
      & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(f171,plain,
    ( ~ v3_ordinal1(sK0)
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f170,f43])).

fof(f43,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f170,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f169,f128])).

fof(f128,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f169,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f168,f45])).

fof(f45,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f168,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl4_2 ),
    inference(resolution,[],[f120,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f120,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f165,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f120,f156])).

fof(f156,plain,
    ( r2_hidden(sK1,sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f155,f45])).

fof(f155,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f154,f43])).

fof(f154,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f153,f42])).

fof(f153,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | spl4_3 ),
    inference(resolution,[],[f125,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f79,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(resolution,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f125,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f163,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f161,f74])).

fof(f74,plain,(
    v1_ordinal1(sK1) ),
    inference(resolution,[],[f50,f43])).

fof(f161,plain,
    ( ~ v1_ordinal1(sK1)
    | spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f159,f125])).

fof(f159,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v1_ordinal1(sK1)
    | spl4_1 ),
    inference(resolution,[],[f149,f53])).

fof(f149,plain,
    ( r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f148,f45])).

fof(f148,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | spl4_1 ),
    inference(subsumption_resolution,[],[f147,f42])).

fof(f147,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | spl4_1 ),
    inference(subsumption_resolution,[],[f141,f43])).

fof(f141,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | spl4_1 ),
    inference(resolution,[],[f117,f84])).

fof(f117,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f146,plain,
    ( spl4_1
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f144,f45])).

fof(f144,plain,
    ( sK0 = sK1
    | spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f143,f42])).

fof(f143,plain,
    ( ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f142,f43])).

fof(f142,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f141,f128])).

fof(f129,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f122,f127,f124])).

fof(f122,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f113,f43])).

fof(f113,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f102,f77])).

fof(f77,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f76,f46])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f76,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f75,f46])).

fof(f75,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f97,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(forward_demodulation,[],[f95,f72])).

fof(f72,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f69,f46])).

fof(f69,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f94,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f93,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f91,f46])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(superposition,[],[f47,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

% (12307)Refutation not found, incomplete strategy% (12307)------------------------------
% (12307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12307)Termination reason: Refutation not found, incomplete strategy

% (12307)Memory used [KB]: 6140
% (12307)Time elapsed: 0.066 s
% (12307)------------------------------
% (12307)------------------------------
% (12318)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (12324)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (12308)Refutation not found, incomplete strategy% (12308)------------------------------
% (12308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12308)Termination reason: Refutation not found, incomplete strategy

% (12308)Memory used [KB]: 10618
% (12308)Time elapsed: 0.090 s
% (12308)------------------------------
% (12308)------------------------------
% (12326)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (12323)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (12327)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (12327)Refutation not found, incomplete strategy% (12327)------------------------------
% (12327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12327)Termination reason: Refutation not found, incomplete strategy

% (12327)Memory used [KB]: 10618
% (12327)Time elapsed: 0.109 s
% (12327)------------------------------
% (12327)------------------------------
% (12316)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (12311)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (12317)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (12318)Refutation not found, incomplete strategy% (12318)------------------------------
% (12318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12318)Termination reason: Refutation not found, incomplete strategy

% (12318)Memory used [KB]: 10618
% (12318)Time elapsed: 0.107 s
% (12318)------------------------------
% (12318)------------------------------
% (12313)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(f121,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f114,f119,f116])).

fof(f114,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f112,f42])).

fof(f112,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f102,f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:21:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (12320)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (12320)Refutation not found, incomplete strategy% (12320)------------------------------
% 0.22/0.48  % (12320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12312)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (12320)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (12320)Memory used [KB]: 1663
% 0.22/0.48  % (12320)Time elapsed: 0.062 s
% 0.22/0.48  % (12320)------------------------------
% 0.22/0.48  % (12320)------------------------------
% 0.22/0.48  % (12322)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (12322)Refutation not found, incomplete strategy% (12322)------------------------------
% 0.22/0.48  % (12322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12322)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (12322)Memory used [KB]: 6140
% 0.22/0.48  % (12322)Time elapsed: 0.064 s
% 0.22/0.48  % (12322)------------------------------
% 0.22/0.48  % (12322)------------------------------
% 0.22/0.49  % (12310)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (12314)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (12308)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (12321)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (12319)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (12309)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (12307)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (12325)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (12309)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f121,f129,f146,f163,f165,f173])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    spl4_2 | spl4_4),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f172])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    $false | (spl4_2 | spl4_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f171,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    v3_ordinal1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f35,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f12])).
% 0.22/0.50  fof(f12,conjecture,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ~v3_ordinal1(sK0) | (spl4_2 | spl4_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f170,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    v3_ordinal1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | (spl4_2 | spl4_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f169,f128])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ~r2_hidden(sK0,sK1) | spl4_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl4_4 <=> r2_hidden(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl4_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f168,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    sK0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    sK0 = sK1 | r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl4_2),
% 0.22/0.50    inference(resolution,[],[f120,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ~r2_hidden(sK1,sK0) | spl4_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl4_2 <=> r2_hidden(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    spl4_2 | spl4_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f164])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    $false | (spl4_2 | spl4_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f120,f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    r2_hidden(sK1,sK0) | spl4_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f155,f45])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    r2_hidden(sK1,sK0) | sK0 = sK1 | spl4_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f154,f43])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1) | sK0 = sK1 | spl4_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f153,f42])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK0 = sK1 | spl4_3),
% 0.22/0.50    inference(resolution,[],[f125,f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | X0 = X1) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f79,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f52,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_tarski(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.22/0.50    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ~r1_tarski(sK0,sK1) | spl4_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f124])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl4_1 | spl4_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    $false | (spl4_1 | spl4_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f161,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    v1_ordinal1(sK1)),
% 0.22/0.50    inference(resolution,[],[f50,f43])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ~v1_ordinal1(sK1) | (spl4_1 | spl4_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f159,f125])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    r1_tarski(sK0,sK1) | ~v1_ordinal1(sK1) | spl4_1),
% 0.22/0.51    inference(resolution,[],[f149,f53])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    r2_hidden(sK0,sK1) | spl4_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f148,f45])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    r2_hidden(sK0,sK1) | sK0 = sK1 | spl4_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f147,f42])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0) | sK0 = sK1 | spl4_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f141,f43])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = sK1 | spl4_1),
% 0.22/0.51    inference(resolution,[],[f117,f84])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    ~r1_tarski(sK1,sK0) | spl4_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f116])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl4_1 <=> r1_tarski(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    spl4_1 | spl4_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f145])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    $false | (spl4_1 | spl4_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f144,f45])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    sK0 = sK1 | (spl4_1 | spl4_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f143,f42])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    ~v3_ordinal1(sK0) | sK0 = sK1 | (spl4_1 | spl4_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f142,f43])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = sK1 | (spl4_1 | spl4_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f141,f128])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ~spl4_3 | ~spl4_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f122,f127,f124])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ~r2_hidden(sK0,sK1) | ~r1_tarski(sK0,sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f113,f43])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~r1_tarski(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f102,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f76,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f75,f46])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0))),
% 0.22/0.51    inference(resolution,[],[f48,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_wellord1(X0,X1) | r4_wellord1(X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~r1_tarski(X1,X0)) )),
% 0.22/0.51    inference(superposition,[],[f97,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f96])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f95,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f69,f46])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.51    inference(equality_resolution,[],[f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(rectify,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f94,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~v2_wellord1(k1_wellord2(X0)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f93,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~v2_wellord1(k1_wellord2(X0)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f91,f46])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~v2_wellord1(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.51    inference(superposition,[],[f47,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).
% 0.22/0.51  % (12307)Refutation not found, incomplete strategy% (12307)------------------------------
% 0.22/0.51  % (12307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12307)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12307)Memory used [KB]: 6140
% 0.22/0.51  % (12307)Time elapsed: 0.066 s
% 0.22/0.51  % (12307)------------------------------
% 0.22/0.51  % (12307)------------------------------
% 0.22/0.51  % (12318)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (12324)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (12308)Refutation not found, incomplete strategy% (12308)------------------------------
% 0.22/0.51  % (12308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12308)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12308)Memory used [KB]: 10618
% 0.22/0.51  % (12308)Time elapsed: 0.090 s
% 0.22/0.51  % (12308)------------------------------
% 0.22/0.51  % (12308)------------------------------
% 0.22/0.51  % (12326)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (12323)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (12327)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (12327)Refutation not found, incomplete strategy% (12327)------------------------------
% 0.22/0.52  % (12327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12327)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12327)Memory used [KB]: 10618
% 0.22/0.52  % (12327)Time elapsed: 0.109 s
% 0.22/0.52  % (12327)------------------------------
% 0.22/0.52  % (12327)------------------------------
% 0.22/0.52  % (12316)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (12311)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (12317)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (12318)Refutation not found, incomplete strategy% (12318)------------------------------
% 0.22/0.52  % (12318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12318)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12318)Memory used [KB]: 10618
% 0.22/0.52  % (12318)Time elapsed: 0.107 s
% 0.22/0.52  % (12318)------------------------------
% 0.22/0.52  % (12318)------------------------------
% 0.22/0.52  % (12313)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ~spl4_1 | ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f114,f119,f116])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ~r2_hidden(sK1,sK0) | ~r1_tarski(sK1,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f112,f42])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~r1_tarski(sK1,sK0)),
% 0.22/0.52    inference(resolution,[],[f102,f44])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (12309)------------------------------
% 0.22/0.52  % (12309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12309)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (12309)Memory used [KB]: 10618
% 0.22/0.52  % (12309)Time elapsed: 0.095 s
% 0.22/0.52  % (12309)------------------------------
% 0.22/0.52  % (12309)------------------------------
% 0.22/0.52  % (12306)Success in time 0.159 s
%------------------------------------------------------------------------------
