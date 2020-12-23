%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 317 expanded)
%              Number of leaves         :   17 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  322 (1001 expanded)
%              Number of equality atoms :   46 ( 175 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f124,f155,f166,f182])).

fof(f182,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f180,f39])).

fof(f39,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(f180,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f179,f118])).

fof(f118,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_3
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f179,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f178,f88])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | ~ r2_xboole_0(sK1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f84,f36])).

fof(f36,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_xboole_0(X1,X0)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f41,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f178,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f177,f37])).

fof(f37,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f177,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f176,f172])).

fof(f172,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f118,f87])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ r2_xboole_0(X1,X2)
      | k1_wellord2(X1) = k2_wellord1(k1_wellord2(X2),X1) ) ),
    inference(resolution,[],[f56,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f176,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f175,f39])).

fof(f175,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(superposition,[],[f145,f123])).

fof(f123,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_4
  <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(forward_demodulation,[],[f144,f73])).

fof(f73,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f63,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f143,f40])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f42,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(f166,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f165,f117,f105])).

fof(f105,plain,
    ( spl4_1
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f165,plain,
    ( r2_xboole_0(sK1,sK0)
    | r2_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f138,f38])).

fof(f38,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f138,plain,
    ( r2_xboole_0(sK1,sK0)
    | sK0 = sK1
    | r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f126,f36])).

fof(f126,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r2_xboole_0(X1,sK0)
      | sK0 = X1
      | r2_xboole_0(sK0,X1) ) ),
    inference(resolution,[],[f47,f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_xboole_0(X0,X1)
      | X0 = X1
      | r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).

fof(f155,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f153,f36])).

fof(f153,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f152,f135])).

fof(f135,plain,
    ( r2_xboole_0(sK0,sK1)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f134,f119])).

fof(f119,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f134,plain,
    ( r2_xboole_0(sK0,sK1)
    | r2_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f128,f38])).

fof(f128,plain,
    ( r2_xboole_0(sK0,sK1)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f125,f39])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_xboole_0(X0,sK1)
      | sK1 = X0
      | r2_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f47,f36])).

fof(f152,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl4_2
    | spl4_3 ),
    inference(resolution,[],[f151,f89])).

fof(f89,plain,(
    ! [X1] :
      ( r2_hidden(sK0,X1)
      | ~ r2_xboole_0(sK0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f84,f39])).

fof(f151,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f150,f95])).

fof(f95,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(resolution,[],[f94,f37])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0)) ) ),
    inference(resolution,[],[f85,f40])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X1),X0) ) ),
    inference(resolution,[],[f43,f40])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f150,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ spl4_2
    | spl4_3 ),
    inference(forward_demodulation,[],[f149,f136])).

fof(f136,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | spl4_3 ),
    inference(resolution,[],[f135,f87])).

fof(f149,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f148,f36])).

fof(f148,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f145,f111])).

fof(f111,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_2
  <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f124,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f115,f121,f117])).

fof(f115,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ r2_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f113,f39])).

fof(f113,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ r2_xboole_0(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f100,f88])).

fof(f100,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_wellord1(k1_wellord2(sK0),X1) = X1 ) ),
    inference(subsumption_resolution,[],[f98,f77])).

fof(f77,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(resolution,[],[f55,f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f98,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X1,sK0)
      | k1_wellord1(k1_wellord2(sK0),X1) = X1 ) ),
    inference(resolution,[],[f46,f39])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(f112,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f103,f109,f105])).

fof(f103,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ r2_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f102,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ r2_xboole_0(sK0,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f99,f89])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_wellord1(k1_wellord2(sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f97,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | v3_ordinal1(X0) ) ),
    inference(resolution,[],[f55,f36])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,sK1)
      | k1_wellord1(k1_wellord2(sK1),X0) = X0 ) ),
    inference(resolution,[],[f46,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:03:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (16378)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (16381)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (16396)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (16399)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (16390)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (16377)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (16391)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (16380)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (16377)Refutation not found, incomplete strategy% (16377)------------------------------
% 0.21/0.51  % (16377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16378)Refutation not found, incomplete strategy% (16378)------------------------------
% 0.21/0.51  % (16378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16378)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16378)Memory used [KB]: 10618
% 0.21/0.51  % (16378)Time elapsed: 0.091 s
% 0.21/0.51  % (16378)------------------------------
% 0.21/0.51  % (16378)------------------------------
% 0.21/0.51  % (16386)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (16379)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (16383)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (16390)Refutation not found, incomplete strategy% (16390)------------------------------
% 0.21/0.51  % (16390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16390)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16390)Memory used [KB]: 6140
% 0.21/0.51  % (16390)Time elapsed: 0.104 s
% 0.21/0.51  % (16390)------------------------------
% 0.21/0.51  % (16390)------------------------------
% 0.21/0.51  % (16385)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (16393)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (16382)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (16399)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f112,f124,f155,f166,f182])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ~spl4_3 | ~spl4_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    $false | (~spl4_3 | ~spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f180,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    v3_ordinal1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f14])).
% 0.21/0.51  fof(f14,conjecture,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~v3_ordinal1(sK0) | (~spl4_3 | ~spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f179,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    r2_xboole_0(sK1,sK0) | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl4_3 <=> r2_xboole_0(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    ~r2_xboole_0(sK1,sK0) | ~v3_ordinal1(sK0) | (~spl4_3 | ~spl4_4)),
% 0.21/0.51    inference(resolution,[],[f178,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1,X0) | ~r2_xboole_0(sK1,X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f84,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v3_ordinal1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_xboole_0(X1,X0) | r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f41,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_ordinal1(X0) | ~v3_ordinal1(X1) | ~r2_xboole_0(X0,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~r2_hidden(sK1,sK0) | (~spl4_3 | ~spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f177,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,sK0) | (~spl4_3 | ~spl4_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f176,f172])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl4_3),
% 0.21/0.51    inference(resolution,[],[f118,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~r2_xboole_0(X1,X2) | k1_wellord2(X1) = k2_wellord1(k1_wellord2(X2),X1)) )),
% 0.21/0.51    inference(resolution,[],[f56,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | ~spl4_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f175,f39])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~spl4_4),
% 0.21/0.51    inference(superposition,[],[f145,f123])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl4_4 <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f144,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f63,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.51    inference(equality_resolution,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f143,f40])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f42,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_wellord1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    spl4_1 | spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f165,f117,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl4_1 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    r2_xboole_0(sK1,sK0) | r2_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f138,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    sK0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    r2_xboole_0(sK1,sK0) | sK0 = sK1 | r2_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f126,f36])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X1] : (~v3_ordinal1(X1) | r2_xboole_0(X1,sK0) | sK0 = X1 | r2_xboole_0(sK0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f47,f39])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_xboole_0(X0,X1) | X0 = X1 | r2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ~spl4_2 | spl4_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    $false | (~spl4_2 | spl4_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f153,f36])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~v3_ordinal1(sK1) | (~spl4_2 | spl4_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f152,f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    r2_xboole_0(sK0,sK1) | spl4_3),
% 0.21/0.51    inference(subsumption_resolution,[],[f134,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ~r2_xboole_0(sK1,sK0) | spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f117])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    r2_xboole_0(sK0,sK1) | r2_xboole_0(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f128,f38])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    r2_xboole_0(sK0,sK1) | sK0 = sK1 | r2_xboole_0(sK1,sK0)),
% 0.21/0.51    inference(resolution,[],[f125,f39])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_ordinal1(X0) | r2_xboole_0(X0,sK1) | sK1 = X0 | r2_xboole_0(sK1,X0)) )),
% 0.21/0.51    inference(resolution,[],[f47,f36])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ~r2_xboole_0(sK0,sK1) | ~v3_ordinal1(sK1) | (~spl4_2 | spl4_3)),
% 0.21/0.51    inference(resolution,[],[f151,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(sK0,X1) | ~r2_xboole_0(sK0,X1) | ~v3_ordinal1(X1)) )),
% 0.21/0.51    inference(resolution,[],[f84,f39])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ~r2_hidden(sK0,sK1) | (~spl4_2 | spl4_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f150,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.21/0.51    inference(resolution,[],[f94,f37])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))) )),
% 0.21/0.51    inference(resolution,[],[f85,f40])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r4_wellord1(X0,k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.51    inference(resolution,[],[f43,f40])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r4_wellord1(X0,X1) | r4_wellord1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r2_hidden(sK0,sK1) | (~spl4_2 | spl4_3)),
% 0.21/0.51    inference(forward_demodulation,[],[f149,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | spl4_3),
% 0.21/0.51    inference(resolution,[],[f135,f87])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~spl4_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f148,f36])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~spl4_2),
% 0.21/0.51    inference(superposition,[],[f145,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl4_2 <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ~spl4_3 | spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f115,f121,f117])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~r2_xboole_0(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f113,f39])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~r2_xboole_0(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.21/0.51    inference(resolution,[],[f100,f88])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_wellord1(k1_wellord2(sK0),X1) = X1) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f98,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | v3_ordinal1(X1)) )),
% 0.21/0.51    inference(resolution,[],[f55,f39])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | v3_ordinal1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.51    inference(flattening,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X1] : (~v3_ordinal1(X1) | ~r2_hidden(X1,sK0) | k1_wellord1(k1_wellord2(sK0),X1) = X1) )),
% 0.21/0.51    inference(resolution,[],[f46,f39])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~spl4_1 | spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f103,f109,f105])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~r2_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f36])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~r2_xboole_0(sK0,sK1) | ~v3_ordinal1(sK1)),
% 0.21/0.51    inference(resolution,[],[f99,f89])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_wellord1(k1_wellord2(sK1),X0) = X0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f97,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | v3_ordinal1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f55,f36])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_ordinal1(X0) | ~r2_hidden(X0,sK1) | k1_wellord1(k1_wellord2(sK1),X0) = X0) )),
% 0.21/0.51    inference(resolution,[],[f46,f36])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (16399)------------------------------
% 0.21/0.51  % (16399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16399)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (16399)Memory used [KB]: 10746
% 0.21/0.51  % (16399)Time elapsed: 0.065 s
% 0.21/0.51  % (16399)------------------------------
% 0.21/0.51  % (16399)------------------------------
% 0.21/0.52  % (16376)Success in time 0.156 s
%------------------------------------------------------------------------------
