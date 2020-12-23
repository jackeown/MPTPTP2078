%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 431 expanded)
%              Number of leaves         :   31 ( 134 expanded)
%              Depth                    :   14
%              Number of atoms          :  568 (2978 expanded)
%              Number of equality atoms :  107 ( 803 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f92,f105,f111,f117,f123,f146,f153,f166,f169,f186,f197,f270,f315])).

fof(f315,plain,
    ( ~ spl8_5
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f289,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f289,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f200,f196])).

fof(f196,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl8_16
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f200,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f87,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f87,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl8_5
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f270,plain,
    ( spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_15 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_15 ),
    inference(subsumption_resolution,[],[f268,f72])).

fof(f72,plain,
    ( sK2 != sK3
    | spl8_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl8_2
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f268,plain,
    ( sK2 = sK3
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_15 ),
    inference(forward_demodulation,[],[f267,f254])).

fof(f254,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl8_5
    | spl8_15 ),
    inference(resolution,[],[f222,f87])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | spl8_15 ),
    inference(resolution,[],[f192,f63])).

fof(f63,plain,(
    ! [X2,X0,X3] :
      ( sP7(X3,X0)
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f63_D])).

fof(f63_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X0)
          | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 )
    <=> ~ sP7(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f192,plain,
    ( ~ sP7(sK1,sK0)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl8_15
  <=> sP7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f267,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl8_3
    | ~ spl8_4
    | spl8_15 ),
    inference(forward_demodulation,[],[f257,f77])).

fof(f77,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl8_3
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f257,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl8_4
    | spl8_15 ),
    inference(resolution,[],[f222,f82])).

fof(f82,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl8_4
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f197,plain,
    ( ~ spl8_15
    | spl8_16
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f188,f66,f194,f190])).

fof(f66,plain,
    ( spl8_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f188,plain,
    ( ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP7(sK1,sK0) ),
    inference(subsumption_resolution,[],[f187,f39])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( sK2 != sK3
        & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,sK0)
        & r2_hidden(sK2,sK0) )
      | ~ v2_funct_1(sK1) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
          | ~ r2_hidden(X5,sK0)
          | ~ r2_hidden(X4,sK0) )
      | v2_funct_1(sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK0)
            & r2_hidden(X2,sK0) )
        | ~ v2_funct_1(sK1) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
            | ~ r2_hidden(X5,sK0)
            | ~ r2_hidden(X4,sK0) )
        | v2_funct_1(sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f187,plain,
    ( ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | ~ sP7(sK1,sK0) ),
    inference(subsumption_resolution,[],[f119,f40])).

fof(f40,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f119,plain,
    ( ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ sP7(sK1,sK0) ),
    inference(resolution,[],[f41,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP7(X3,X0) ) ),
    inference(general_splitting,[],[f62,f63_D])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f186,plain,
    ( spl8_1
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl8_1
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f184,f124])).

fof(f124,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f120,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f120,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f184,plain,
    ( ~ v1_relat_1(sK1)
    | spl8_1
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f183,f39])).

fof(f183,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl8_1
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f182,f68])).

fof(f68,plain,
    ( ~ v2_funct_1(sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f182,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl8_14 ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl8_14 ),
    inference(superposition,[],[f53,f165])).

fof(f165,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl8_14
  <=> sK4(sK1) = sK5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f53,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f169,plain,
    ( ~ spl8_8
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl8_8
    | spl8_13 ),
    inference(subsumption_resolution,[],[f167,f126])).

fof(f126,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f125,f124])).

fof(f125,plain,
    ( r1_tarski(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f118,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f118,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f41,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f167,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ spl8_8
    | spl8_13 ),
    inference(resolution,[],[f161,f129])).

fof(f129,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1),X0)
        | ~ r1_tarski(k1_relat_1(sK1),X0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f104,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f104,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_8
  <=> r2_hidden(sK4(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f161,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl8_13
  <=> r2_hidden(sK4(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f166,plain,
    ( ~ spl8_13
    | spl8_14
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f157,f143,f163,f159])).

fof(f143,plain,
    ( spl8_12
  <=> ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f157,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ r2_hidden(sK4(sK1),sK0)
    | ~ spl8_12 ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f153,plain,
    ( ~ spl8_9
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl8_9
    | spl8_11 ),
    inference(subsumption_resolution,[],[f151,f126])).

fof(f151,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ spl8_9
    | spl8_11 ),
    inference(resolution,[],[f133,f141])).

fof(f141,plain,
    ( ~ r2_hidden(sK5(sK1),sK0)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_11
  <=> r2_hidden(sK5(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f133,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1),X0)
        | ~ r1_tarski(k1_relat_1(sK1),X0) )
    | ~ spl8_9 ),
    inference(resolution,[],[f110,f57])).

fof(f110,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl8_9
  <=> r2_hidden(sK5(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f146,plain,
    ( ~ spl8_11
    | spl8_12
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f135,f114,f90,f143,f139])).

fof(f90,plain,
    ( spl8_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f114,plain,
    ( spl8_10
  <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f135,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1))
        | ~ r2_hidden(sK5(sK1),sK0)
        | ~ r2_hidden(X1,sK0)
        | sK5(sK1) = X1 )
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(superposition,[],[f91,f116])).

fof(f116,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f91,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | X4 = X5 )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f123,plain,(
    spl8_7 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl8_7 ),
    inference(subsumption_resolution,[],[f121,f54])).

fof(f121,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl8_7 ),
    inference(subsumption_resolution,[],[f120,f100])).

fof(f100,plain,
    ( ~ v1_relat_1(sK1)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f117,plain,
    ( ~ spl8_7
    | spl8_10
    | spl8_1 ),
    inference(avatar_split_clause,[],[f112,f66,f114,f98])).

fof(f112,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_relat_1(sK1)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f95,f39])).

fof(f95,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl8_1 ),
    inference(resolution,[],[f68,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,
    ( ~ spl8_7
    | spl8_9
    | spl8_1 ),
    inference(avatar_split_clause,[],[f106,f66,f108,f98])).

fof(f106,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f94,f39])).

fof(f94,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl8_1 ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f105,plain,
    ( ~ spl8_7
    | spl8_8
    | spl8_1 ),
    inference(avatar_split_clause,[],[f96,f66,f102,f98])).

fof(f96,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f93,f39])).

fof(f93,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl8_1 ),
    inference(resolution,[],[f68,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,
    ( spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f42,f90,f66])).

fof(f42,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f43,f85,f66])).

fof(f43,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f44,f80,f66])).

fof(f44,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f45,f75,f66])).

fof(f45,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f46,f70,f66])).

fof(f46,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (11627)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.46  % (11640)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.47  % (11627)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f330,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f92,f105,f111,f117,f123,f146,f153,f166,f169,f186,f197,f270,f315])).
% 0.20/0.47  fof(f315,plain,(
% 0.20/0.47    ~spl8_5 | ~spl8_16),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f314])).
% 0.20/0.47  fof(f314,plain,(
% 0.20/0.47    $false | (~spl8_5 | ~spl8_16)),
% 0.20/0.47    inference(subsumption_resolution,[],[f289,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.47  fof(f289,plain,(
% 0.20/0.47    ~r1_tarski(k1_xboole_0,sK2) | (~spl8_5 | ~spl8_16)),
% 0.20/0.47    inference(backward_demodulation,[],[f200,f196])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~spl8_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f194])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    spl8_16 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.47  fof(f200,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK2) | ~spl8_5),
% 0.20/0.47    inference(resolution,[],[f87,f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    r2_hidden(sK2,sK0) | ~spl8_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl8_5 <=> r2_hidden(sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.48  fof(f270,plain,(
% 0.20/0.48    spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_15),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f269])).
% 0.20/0.48  fof(f269,plain,(
% 0.20/0.48    $false | (spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_15)),
% 0.20/0.48    inference(subsumption_resolution,[],[f268,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    sK2 != sK3 | spl8_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl8_2 <=> sK2 = sK3),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.48  fof(f268,plain,(
% 0.20/0.48    sK2 = sK3 | (~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_15)),
% 0.20/0.48    inference(forward_demodulation,[],[f267,f254])).
% 0.20/0.48  fof(f254,plain,(
% 0.20/0.48    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl8_5 | spl8_15)),
% 0.20/0.48    inference(resolution,[],[f222,f87])).
% 0.20/0.48  fof(f222,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | spl8_15),
% 0.20/0.48    inference(resolution,[],[f192,f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X2,X0,X3] : (sP7(X3,X0) | ~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f63_D])).
% 0.20/0.48  fof(f63_D,plain,(
% 0.20/0.48    ( ! [X0,X3] : (( ! [X2] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) ) <=> ~sP7(X3,X0)) )),
% 0.20/0.48    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    ~sP7(sK1,sK0) | spl8_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f190])).
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    spl8_15 <=> sP7(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.48  fof(f267,plain,(
% 0.20/0.48    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl8_3 | ~spl8_4 | spl8_15)),
% 0.20/0.48    inference(forward_demodulation,[],[f257,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl8_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl8_3 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.48  fof(f257,plain,(
% 0.20/0.48    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl8_4 | spl8_15)),
% 0.20/0.48    inference(resolution,[],[f222,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    r2_hidden(sK3,sK0) | ~spl8_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl8_4 <=> r2_hidden(sK3,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    ~spl8_15 | spl8_16 | ~spl8_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f188,f66,f194,f190])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl8_1 <=> v2_funct_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP7(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f187,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v1_funct_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ((sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) | ~v2_funct_1(sK1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f28,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) | ~v2_funct_1(sK1)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.48    inference(rectify,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.48    inference(negated_conjecture,[],[f10])).
% 0.20/0.48  fof(f10,conjecture,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | ~sP7(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f119,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~sP7(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f41,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | k1_xboole_0 = X1 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~sP7(X3,X0)) )),
% 0.20/0.48    inference(general_splitting,[],[f62,f63_D])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.48    inference(flattening,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f186,plain,(
% 0.20/0.48    spl8_1 | ~spl8_14),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f185])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    $false | (spl8_1 | ~spl8_14)),
% 0.20/0.48    inference(subsumption_resolution,[],[f184,f124])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f120,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.20/0.48    inference(resolution,[],[f41,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    ~v1_relat_1(sK1) | (spl8_1 | ~spl8_14)),
% 0.20/0.48    inference(subsumption_resolution,[],[f183,f39])).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl8_1 | ~spl8_14)),
% 0.20/0.48    inference(subsumption_resolution,[],[f182,f68])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ~v2_funct_1(sK1) | spl8_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f66])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl8_14),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f181])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    sK4(sK1) != sK4(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl8_14),
% 0.20/0.48    inference(superposition,[],[f53,f165])).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    sK4(sK1) = sK5(sK1) | ~spl8_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f163])).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    spl8_14 <=> sK4(sK1) = sK5(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0] : (sK4(X0) != sK5(X0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(rectify,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ~spl8_8 | spl8_13),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f168])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    $false | (~spl8_8 | spl8_13)),
% 0.20/0.48    inference(subsumption_resolution,[],[f167,f126])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f125,f124])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    r1_tarski(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.20/0.48    inference(resolution,[],[f118,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    v4_relat_1(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f41,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    ~r1_tarski(k1_relat_1(sK1),sK0) | (~spl8_8 | spl8_13)),
% 0.20/0.48    inference(resolution,[],[f161,f129])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK4(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X0)) ) | ~spl8_8),
% 0.20/0.48    inference(resolution,[],[f104,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | ~spl8_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f102])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl8_8 <=> r2_hidden(sK4(sK1),k1_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    ~r2_hidden(sK4(sK1),sK0) | spl8_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f159])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    spl8_13 <=> r2_hidden(sK4(sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    ~spl8_13 | spl8_14 | ~spl8_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f157,f143,f163,f159])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    spl8_12 <=> ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    sK4(sK1) = sK5(sK1) | ~r2_hidden(sK4(sK1),sK0) | ~spl8_12),
% 0.20/0.48    inference(equality_resolution,[],[f144])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0)) ) | ~spl8_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f143])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    ~spl8_9 | spl8_11),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f152])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    $false | (~spl8_9 | spl8_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f151,f126])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    ~r1_tarski(k1_relat_1(sK1),sK0) | (~spl8_9 | spl8_11)),
% 0.20/0.48    inference(resolution,[],[f133,f141])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ~r2_hidden(sK5(sK1),sK0) | spl8_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f139])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    spl8_11 <=> r2_hidden(sK5(sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK5(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X0)) ) | ~spl8_9),
% 0.20/0.48    inference(resolution,[],[f110,f57])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | ~spl8_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f108])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    spl8_9 <=> r2_hidden(sK5(sK1),k1_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    ~spl8_11 | spl8_12 | ~spl8_6 | ~spl8_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f135,f114,f90,f143,f139])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl8_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    spl8_10 <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(sK5(sK1),sK0) | ~r2_hidden(X1,sK0) | sK5(sK1) = X1) ) | (~spl8_6 | ~spl8_10)),
% 0.20/0.48    inference(superposition,[],[f91,f116])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~spl8_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f114])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | X4 = X5) ) | ~spl8_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f90])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    spl8_7),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    $false | spl8_7),
% 0.20/0.49    inference(subsumption_resolution,[],[f121,f54])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl8_7),
% 0.20/0.49    inference(subsumption_resolution,[],[f120,f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ~v1_relat_1(sK1) | spl8_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    spl8_7 <=> v1_relat_1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ~spl8_7 | spl8_10 | spl8_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f112,f66,f114,f98])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1) | spl8_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f95,f39])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl8_1),
% 0.20/0.49    inference(resolution,[],[f68,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ~spl8_7 | spl8_9 | spl8_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f106,f66,f108,f98])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | spl8_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f94,f39])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl8_1),
% 0.20/0.49    inference(resolution,[],[f68,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ~spl8_7 | spl8_8 | spl8_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f96,f66,f102,f98])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | spl8_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f93,f39])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl8_1),
% 0.20/0.49    inference(resolution,[],[f68,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK4(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl8_1 | spl8_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f42,f90,f66])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0) | v2_funct_1(sK1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ~spl8_1 | spl8_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f85,f66])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ~spl8_1 | spl8_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f80,f66])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ~spl8_1 | spl8_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f75,f66])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ~spl8_1 | ~spl8_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f46,f70,f66])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (11627)------------------------------
% 0.20/0.49  % (11627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (11627)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (11627)Memory used [KB]: 10874
% 0.20/0.49  % (11627)Time elapsed: 0.063 s
% 0.20/0.49  % (11627)------------------------------
% 0.20/0.49  % (11627)------------------------------
% 0.20/0.49  % (11618)Success in time 0.13 s
%------------------------------------------------------------------------------
