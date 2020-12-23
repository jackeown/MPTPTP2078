%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 197 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  281 (1034 expanded)
%              Number of equality atoms :   79 ( 356 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f166,f174,f184,f195,f199,f212,f220])).

fof(f220,plain,(
    ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f128,f214])).

fof(f214,plain,
    ( sK1 = k4_relat_1(sK0)
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f49,f211])).

fof(f211,plain,
    ( sK0 = k4_relat_1(sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl2_6
  <=> sK0 = k4_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f49,plain,(
    sK1 = k4_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f128,plain,(
    sK1 != k4_relat_1(sK0) ),
    inference(global_subsumption,[],[f27,f31,f32,f126])).

fof(f126,plain,
    ( sK1 != k4_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0) ),
    inference(superposition,[],[f30,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f30,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f212,plain,
    ( ~ spl2_2
    | spl2_6
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f207,f188,f181,f209,f163])).

fof(f163,plain,
    ( spl2_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f181,plain,
    ( spl2_3
  <=> k4_relat_1(sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f188,plain,
    ( spl2_4
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f207,plain,
    ( sK0 = k4_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f206,f183])).

fof(f183,plain,
    ( k4_relat_1(sK1) = k2_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f181])).

fof(f206,plain,
    ( ~ v2_funct_1(sK1)
    | sK0 = k2_funct_1(sK1)
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f205])).

fof(f205,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | ~ v2_funct_1(sK1)
    | sK0 = k2_funct_1(sK1)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f153,f190])).

fof(f190,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f188])).

fof(f153,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | sK0 = k2_funct_1(sK1) ),
    inference(global_subsumption,[],[f25,f26,f31,f32,f152])).

fof(f152,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK1)
    | sK0 = k2_funct_1(sK1) ),
    inference(trivial_inequality_removal,[],[f151])).

fof(f151,plain,
    ( k2_relat_1(sK1) != k2_relat_1(sK1)
    | k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK1)
    | sK0 = k2_funct_1(sK1) ),
    inference(forward_demodulation,[],[f145,f28])).

fof(f28,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f145,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK1)
    | k1_relat_1(sK0) != k2_relat_1(sK1)
    | sK0 = k2_funct_1(sK1) ),
    inference(superposition,[],[f41,f29])).

fof(f29,plain,(
    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f199,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f194,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f194,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl2_5
  <=> r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f195,plain,
    ( spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f157,f192,f188])).

fof(f157,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(global_subsumption,[],[f25,f31,f156])).

fof(f156,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f155,f28])).

fof(f155,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f147,f35])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f147,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(superposition,[],[f38,f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f184,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f61,f163,f181])).

fof(f61,plain,
    ( ~ v2_funct_1(sK1)
    | k4_relat_1(sK1) = k2_funct_1(sK1) ),
    inference(global_subsumption,[],[f26,f52])).

fof(f52,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | k4_relat_1(sK1) = k2_funct_1(sK1) ),
    inference(resolution,[],[f25,f39])).

fof(f174,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f161,f34])).

fof(f34,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f161,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl2_1
  <=> v2_funct_1(k6_relat_1(k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f166,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f150,f163,f159])).

fof(f150,plain,
    ( v2_funct_1(sK1)
    | ~ v2_funct_1(k6_relat_1(k2_relat_1(sK0))) ),
    inference(global_subsumption,[],[f25,f26,f31,f32,f149])).

fof(f149,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,
    ( k2_relat_1(sK1) != k2_relat_1(sK1)
    | ~ v2_funct_1(k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(forward_demodulation,[],[f143,f28])).

fof(f143,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(sK0) != k2_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(superposition,[],[f42,f29])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:45:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (22094)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (22102)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (22094)Refutation not found, incomplete strategy% (22094)------------------------------
% 0.22/0.51  % (22094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22108)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (22094)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22094)Memory used [KB]: 10618
% 0.22/0.51  % (22094)Time elapsed: 0.064 s
% 0.22/0.51  % (22094)------------------------------
% 0.22/0.51  % (22094)------------------------------
% 0.22/0.52  % (22108)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f166,f174,f184,f195,f199,f212,f220])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    ~spl2_6),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f216])).
% 0.22/0.52  fof(f216,plain,(
% 0.22/0.52    $false | ~spl2_6),
% 0.22/0.52    inference(subsumption_resolution,[],[f128,f214])).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    sK1 = k4_relat_1(sK0) | ~spl2_6),
% 0.22/0.52    inference(backward_demodulation,[],[f49,f211])).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    sK0 = k4_relat_1(sK1) | ~spl2_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f209])).
% 0.22/0.52  fof(f209,plain,(
% 0.22/0.52    spl2_6 <=> sK0 = k4_relat_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    sK1 = k4_relat_1(k4_relat_1(sK1))),
% 0.22/0.52    inference(resolution,[],[f25,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    sK1 != k4_relat_1(sK0)),
% 0.22/0.52    inference(global_subsumption,[],[f27,f31,f32,f126])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    sK1 != k4_relat_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v2_funct_1(sK0)),
% 0.22/0.52    inference(superposition,[],[f30,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    sK1 != k2_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    v1_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    v2_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f212,plain,(
% 0.22/0.52    ~spl2_2 | spl2_6 | ~spl2_3 | ~spl2_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f207,f188,f181,f209,f163])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    spl2_2 <=> v2_funct_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    spl2_3 <=> k4_relat_1(sK1) = k2_funct_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    spl2_4 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    sK0 = k4_relat_1(sK1) | ~v2_funct_1(sK1) | (~spl2_3 | ~spl2_4)),
% 0.22/0.52    inference(forward_demodulation,[],[f206,f183])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    k4_relat_1(sK1) = k2_funct_1(sK1) | ~spl2_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f181])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    ~v2_funct_1(sK1) | sK0 = k2_funct_1(sK1) | ~spl2_4),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f205])).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0)) | ~v2_funct_1(sK1) | sK0 = k2_funct_1(sK1) | ~spl2_4),
% 0.22/0.52    inference(forward_demodulation,[],[f153,f190])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl2_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f188])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v2_funct_1(sK1) | sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(global_subsumption,[],[f25,f26,f31,f32,f152])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v2_funct_1(sK1) | sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f151])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    k2_relat_1(sK1) != k2_relat_1(sK1) | k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v2_funct_1(sK1) | sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f145,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v2_funct_1(sK1) | k1_relat_1(sK0) != k2_relat_1(sK1) | sK0 = k2_funct_1(sK1)),
% 0.22/0.52    inference(superposition,[],[f41,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    v1_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    spl2_5),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f196])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    $false | spl2_5),
% 0.22/0.52    inference(resolution,[],[f194,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | spl2_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f192])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    spl2_5 <=> r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    spl2_4 | ~spl2_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f157,f192,f188])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.52    inference(global_subsumption,[],[f25,f31,f156])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | k2_relat_1(sK0) = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f155,f28])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))),
% 0.22/0.52    inference(forward_demodulation,[],[f147,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    k1_relat_1(sK1) = k1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))),
% 0.22/0.52    inference(superposition,[],[f38,f29])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    spl2_3 | ~spl2_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f61,f163,f181])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ~v2_funct_1(sK1) | k4_relat_1(sK1) = k2_funct_1(sK1)),
% 0.22/0.52    inference(global_subsumption,[],[f26,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | k4_relat_1(sK1) = k2_funct_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f25,f39])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    spl2_1),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    $false | spl2_1),
% 0.22/0.52    inference(resolution,[],[f161,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ~v2_funct_1(k6_relat_1(k2_relat_1(sK0))) | spl2_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f159])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    spl2_1 <=> v2_funct_1(k6_relat_1(k2_relat_1(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    ~spl2_1 | spl2_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f150,f163,f159])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    v2_funct_1(sK1) | ~v2_funct_1(k6_relat_1(k2_relat_1(sK0)))),
% 0.22/0.52    inference(global_subsumption,[],[f25,f26,f31,f32,f149])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ~v2_funct_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f148])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    k2_relat_1(sK1) != k2_relat_1(sK1) | ~v2_funct_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f143,f28])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ~v2_funct_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k1_relat_1(sK0) != k2_relat_1(sK1) | v2_funct_1(sK1)),
% 0.22/0.52    inference(superposition,[],[f42,f29])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (22108)------------------------------
% 0.22/0.52  % (22108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22108)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (22108)Memory used [KB]: 10746
% 0.22/0.52  % (22108)Time elapsed: 0.084 s
% 0.22/0.52  % (22108)------------------------------
% 0.22/0.52  % (22108)------------------------------
% 0.22/0.52  % (22110)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (22087)Success in time 0.152 s
%------------------------------------------------------------------------------
